import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard105
open N4R2OuterLeftReplay

-- Cycle fingerprint 00c4a225d149bd5b0884159ae197de1e629f37e609058772543980c25ba074bd.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 01aa0fc07f64849656e2d848bac1e52c723fcd8c362163d56fd64bee4e6f3c24.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 02748c6e69455eb65ae7d2f2f1587aa4993b1b2dc6428278570396a0dbc34b1b.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 12 1]

-- Cycle fingerprint 03dd637c2441e8901f32db038c8e626082edf8994e8881a43353c6b730c4adc4.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 0577f5d488dae372357350d0337c1742bad3cc1da088beeb048a8165d91386ff.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint 061240d93f1afe1ae22af9d0c07f1ff6da2341122a3b1a476c77c3ea9bfae46c.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 0]

-- Cycle fingerprint 06ec53b528fb2a4d704d53f85dff1a54d4b79ad94cf6117c16259f3ea5c50d45.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 0740f8d99f450a8fc0a8c3c8413816d71f4a5ae536ba0eb770208466a02f348c.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 0775d6d0e4afbd589ec92122a248f4cc0d90caa8e69131c7826437cc1be6ddcb.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 095395eb08c1f1382fc76411211003c7ace3cfbaba47a8611a11284c217ffdba.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 11 0, .gapLower 0 4, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 0ac4439b1ddad1bc3ef9278cd6fd6732f0f586230f58d8ef5fb81ee51d255727.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 0ba7c0ed899265874d5227d3691ad4ce8a3ea3f1b7109c55778ec2ce6df078c8.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 0c98bf21e16ab2bd195a14a0c3d6e390f5e105f3663608f79c2e83115c5c04bf.
def localCycle00012 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 0d52f419d69e838b60e81628696380c851d869700e4477da22bf0dd7433d51f7.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 10371200cc2610d4eee4fefbdf39f9b9461123b3db4dc77f05c230cc92c280db.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 2 0]

-- Cycle fingerprint 10b5cf654ce4c73582c1a9bf67ea3f76df722999b33383a73caa6a402f31a7fa.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 13e7b5ced78fd0e840d20a53a9fe69c9a062d4700c94298d20eeb4046ff7b89d.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 14c083c6c9617ad0d7738896e55a58f0de4ef468a9e4d0256ec2f512e29ce8d9.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 151df1b8750c4bb168fc5e525002403f3b13f35dd3e76af5afa106040f6884a1.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 15c28a89db4d09daea2be7e61e945ea0327d05c21d2797ddd9905c12eab23a0d.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 170d5b8ba61f3400511e95308456f0d21b114ad2a7f2c304935dfd62241730d5.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 185c9b343eac444b7ea3a7c821b3e7155d92d3c61c1fb1dc98a95d93e40cbf97.
def localCycle00021 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 6 5]

-- Cycle fingerprint 1c4b431bf1a2a5cdd477c64f061c13f520d8dd4403b67b06a4cb3215e26fe944.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 1c8c5d5c007056d6695139dd87f6e85116542d338fa226c79f943340b3fbe923.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 1cf0f10abecb55b66087c6b8c5075749534064326f27e14b367bab8a27c886fe.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 1d503706b62587102934d26c8d7a74d7131453e8eda2cc66d73545d49f9fe9fc.
def localCycle00025 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 4 3]

-- Cycle fingerprint 1e25f01c0ef1202da1cde51e07a33074a799e35060aebc567682ac63007abc7d.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 24270c63e3ad3d46e581a9913c0cdeecf6b56c8d7f26d6b38027669dfa1ead91.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 248034175f2b19e3989cd9a3e3ec4ab318483fb5fbdf33ff04803a88d0ebfb9b.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 248bb1b1ee4cc0ee381c264dca8b71fa356a86bd4af094156e23359a5574ea84.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 249e085f20922f98dd145e767f8f3785edec72c792482fa5fdea8aaf85ab0118.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 25904c43a9a6848ed7154db27c9ec3678981a8e25f23252b88c73525a249b3a9.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 28bf3a0b67d029d28fc107e57046ff33e6d0a97823f2d518822acbb43bd95269.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 2a7341e42bfaa7b486b88b9eecaf9eb27eacb4bf0e95efe865f8bfcc4e0a27c0.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 2c994e5e73bdcfcc0d66c2ce87f1e6c585a5ffb8ca9a18b0635f37c1dd34dbb7.
def localCycle00034 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 5]

-- Cycle fingerprint 2cb4747cb17f504d5cfef2733117a12bf9b5f0c4f46fde05b3d3fa394533ef45.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 2ccfdab729563dc7e2e5fdb80ede1d4ecdc6741bb40a563594b250b613dafbc7.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 2e32a0f6c27015183eaf82c3b9e99140c2cfc0b63e8b5c68331d1c5ad687fdde.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 303d4a82c0c7ffa7c734bd58be0ce22a8acbaabcb561742e4eac69194aef0228.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 310940e32d672056fbaf7879aac76f36f04c16016c639decf850b9904ea1334f.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 31a2aeeffa4f756e197557229612935b1e1777025a1d69619234a6e89a36b041.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, -2, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 0, .triangle 34 2, .triangle 13 0, .gapLower 0 2]

-- Cycle fingerprint 3341f83260aef067508222d81de9cfbb8ba34589a0429393e4aaa6b1a65d50ad.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 3600fbde3158584c6067c07ab1376dbfe2829ac2fa040d9f0a4325e1d7918ce7.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3975a7be970659d369510403ef8c675c11d5e120c18445b147f09100fe9c38f5.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 3a4963b24c42d89670a482c34ca8b33b9d5f3090292e7551ad9788281ed9a334.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0, .triangle 0 0]

-- Cycle fingerprint 3b1c4be8644e9520705c01e4060851ae57260f62b1f65b90177ce8a2c64ae6f9.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 3b2e44f88ccee8ea304e6d434b432682a5164975f498a831bfbf34e2b8f693b6.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 3b397ac5093c3f277f1a31e6d386d3e24baa43162029346a67861de54f213786.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3b73f2f995aab56b3709a70e448a88048827c97401d51955133e01ee0d560d08.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3d296040d58ce7b8f8fc78ad2ee0cb836afeb2c50323b987feaa1f1e66df3394.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-1, 0, -1, 0, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 3dee73ce0a66ee2884970051b903cc12649f4b70c58acc9ef9e6ebb8cc9af7dc.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 3e29882bf92c7b7a9b5888906a579e40c7d41a97c686298bfe8587a5223588d2.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 3f35071fcff8f20a13a70171281920e220a3e3d2d7e44085e84915efae703c52.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 3f645229545b535da44110af80b4a256a6c85c94b1752210bf1c082f69cb5bdd.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 3fff60832d2a90ac51b75061aad9b7992ae79eb3a42a8fc597e96e5b3a7c5532.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 404de070340ec40b7a4cd37f78e8f0f1836e33523357d30c8c9ba1606882d740.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 411b680c3f0a65f5fa4bbd2938f5f168c7b6d02f2b489b8ebc279bd471a517ea.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0]

-- Cycle fingerprint 412c4eb5dee53768bdbac9685ab3459ac237899f1874f62a6cb409cb3bb748d2.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4242ae111ebcfae266b45dc965b281dd8b0c3b5525d368fc4cb4b8acbb68019d.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 440fe64d248d2f0e84b2dcbf31059e7a9ce6984a98b8b25d9453b566054207e8.
def localCycle00059 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 44235bad545f4efba99b97882b1eb9251383f6af587cf8816644f9e12f0dc365.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 45f0c95fce5f281b7ffd9f19de684343b840059e7ed19c28688616e9e9c77a1e.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 4686c73765f27b888025a6f53c8f6978f1b4f204791802e3ebfba3c4e1c90b70.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 0]

-- Cycle fingerprint 472c94981e9545c4b0bf5e713dcdf9d5d5f711db466cea1bf08604b5e61de0ca.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint 4843d1c71466793e925f6cd254bf8f0df31a524c6001a7cb760e14211343a5b2.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4a065aed7a121b06a469b29bcc98ddd06ef80616a1822c97471517e366db563f.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 4f30657e5caf955a2858525d0f95599a0e11f0b10d048a2c5cdb4cf3b5a459f3.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4fb8312451771b45903f1d8aa6f86e97d72abd93fb66bba0c353fc3a88c9e2ba.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 12 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 50316ea408a0479278ac30009110c272ad9d7be94e63d47d6869c99e6495fac2.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 5045f08e7634c5aa7da3da9ec8bf40d75b930a199f04e0d3e569af5fbc07ab8d.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 50a9306ff9a7e92a354a1b45edc70ce7465781b689ec6167cdcfab17049af60a.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 50b2ba7908da3c34a4175a4ec0656ca29b1d87ef070fdfc8c21d3f41d75652cf.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 5 4]

-- Cycle fingerprint 516a6e6656257f1b84f3cdad4264a59f0b86a73cf93bd3017c3b79dce2bf6ec6.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 5196b3f94ee82c11cf263cbee308b312cc3317945f019d32899a33ee34b67b38.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 520af84b4eb60f8a066caf076f76868f44b49a9b19d4fca2debd4e6ff66c115b.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 52890d41ef47f90b0b8b1fadc377e67dca76feddbf8370f23dea94adcf89f8ce.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 5370ea44c2031bd5019985e4cd51c1c5355b2238087251af4199ff00e5270a69.
def localCycle00076 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 537e4340c3f8bb91e8bb50c941f207643ce1c6caa3041d73a3a1898353da0fd9.
def localCycle00077 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 551b12f3b524fab9e72a76cd74cdbe98fa79b1e959ca82bf998b71ad9b65dde7.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 58bc6f473c3a3027a662f35629403ac8ae13ab2337a940c7be116472b63b00c8.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 0, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 58beef1a75d8dd1b02b3d10071532ce283f5c61d4bf2f74f902f1df781c63bfc.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 2 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 58c5ba24f045893b5a6cbbc25c2531bc7d0c390fa66a19c2f8b0d98775ec4d63.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 592b0a7a219d2f3682278953fadc7fca4f44a373c0998f60897c692c33e79eb7.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 22 0, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 59ef1363cb88e534cac0e8717614233a8facba2850064af0f29822c6cf8f9e76.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 5ae80a5216f2fdfc38ef1f31e824179af6262f039f9e66b5733f075c961379c6.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5]
    constant := ![-1, -3, -1, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2]

-- Cycle fingerprint 5dce886cc8f3166e2a784303c8fc3030f8cba966337d8391e71c439341e8de50.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 5e0de23772d0f7fb221fca05f3fbbf55b46f110ca4d5e83aef347c0c7608387f.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 603d5514383a98860ee82ad589fb6e2d4f0c2fb29e789fea344e45cbf7a2319c.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint 607008590e5d9c245e9f264c319867a199e796760d6cf1d108414eaf142dbfc6.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60c8fdf23d554a45536e53c976a6aed40ceb59900327bac9eb8837933d7da334.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 614c802b885eb5ece8a4f0e86b444029ef71c05c3030d87216bb8f3d14863928.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 615f8d9288dc8d4bf31a7c165bb30837ef57ac0e90e3d77477398e530b46c05c.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 6183b963c8d2b63e2658639319e48c3900717b422b61b6bb3022681d48b9e233.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -3, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 62dc89605dd816ae2dd89fad39d3da79ca2237da9ceeb07fcdddc9f85ee109fb.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 630fccfe120ebfbfc3942e325d03632c2de45b9c685683c019d67fd6a85c95b6.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 3 0]

-- Cycle fingerprint 645a8ab4a62f6f7a0a2a279d7110dd566ca67b68457883c52d832337bbce2202.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 65adf0789b1117dee13e5e2ce1db5d70ee9bd1781e606e2b3fe1f2df6941cd09.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 6650e12a8a3dfc54b51d84123bce7740cc223482fa5b81debf72d779969165a9.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 67c8dfb100e97c062a7caf35fe03e0bed9d9e36cb661fe2b0a113b33ad5b71d0.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 6a8b3885782a7c22a75b478281ceae9f99c35722b871978dae3572057295fea8.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 6b07e4a28729e5dbce620930295ff70bca59bc947a419f0f033bcbceb4e254c8.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 6c76673ba5e64898338c8473825f0fda64156d7bc575097897ac9287e5915d8a.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 6d04c4ea559581ae30b8c363a1b8887db00a3ecea9969084565430a5b9599da1.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00103 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6de93eb111f9b6cf029d411d60af455350cfc57ab9fb9e18365b9b972f479121.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6de94747e780c4a48636a37c668dc0a84f2760918b43807a2d1ce91ce0176e77.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 6e5f2e1660748d00faf79e37aef60ea92d473b33de9b2bbdb8f813952ab4a463.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 70167ee7e4500f4270aad863be52c52e8ea5d02fd574cc93db22342978b18715.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 71512eb0c44cc43f8f5f55d7c19ba9d1af78cf4467758333a50b55e7645d61d5.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 727af6a62f70b57bac8e3a82817057b2084d9e1f58624848c41f19ca57635966.
def localCycle00109 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 73bc42003671aa0d62bb754e765911b34899ee2c8035d4cad1cfb77408148e68.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 73cd70b57653f5325171b6582759746c0ba9568e5b81a98f8a1e1a7125787a73.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 74127b2813beabab84baf8605bd7f7a75408970d89a67a07e613a9b0c37f1b33.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 74563db66bd0320139cf94ba256bff2fecef2dbcdd552819cb1692a801a7ed1f.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 74f4b284f52ff85e05aa5434497991fd1ad078fce49c7f66034e7298f0db6b23.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 3 0]

-- Cycle fingerprint 837ac5cf4a53538fa6b6dad39e85527b61d3d86dda133e0f391608ef36a4d8e8.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 837d360ea4958266097cb3c842be6b7c03ff34e0a84f234dc02e864a990a8a89.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -2, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 84b75135b28c35844954271a97847c5ef7b620c80e93330ce3cde16829f6f310.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 85a9f3f3bd5faaae78435e2fc92cb349386c088fe7f50d93b6b79a66cf5bc2e7.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 86687ee51148f06cf2b189637bcc9b48aee9aa8299cff8456ea783e1980c9a8a.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 881b409489d6575fdfa72335b4398aeacda3fede23b2a1aa9f802c8e92eee129.
def localCycle00121 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 88a2d0edd810ca61e656dc0c6a020c6e43baaeca9ab7178af0f609c81e203ee5.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 89b4e233b729f39961a5c45f7c132eea755727115e0c65f35a8c3034288636d3.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4]
    constant := ![-1, -3, -1, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2]

-- Cycle fingerprint 8c1863ea9ef9d8fa7b3c136687b7fbc7cfbfab394cb8610da352906eee78b46e.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 8de3f290ca9e76ce262c4f1256178e113517fc591211187cbb084a7a354de443.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, -1, -1, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 8e7fa033d30293ae5932057970fba68cf45afee38cf8e0ace21919818818f88f.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 915fbeea49634d655fb1ab6e2cd551bd75ca335142d2548029437e75bc6df3fb.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 93c25ddd41e2238b29e3abfb79db832ddf844be81b32c634ea376b2911847e60.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 94e3c201d8fcf9b57875196ab68e8fec9019c0bdd086eff87959167135d685dc.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, -2, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 12 0, .gapLower 0 2]

-- Cycle fingerprint 97a27b38f45371da99c248c4d29d3e685b4d60bc4e9cc153c0d7d40563c6b8a7.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 97cabdd7e5f0efe0d6abe15e912d52eaecd7c286e254df3c749e949182aa320a.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 984299c5a6bb6670089c506b6e8fec74a50f9a9c3253dc87ac105a63ffdabb08.
def localCycle00133 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 98dcd60152f2082f9e614cda90c7f85898a58a86657cbf4ff931f45911b2225a.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 9ab84f82d6fd276fee88cc15659f10daeb73633e3f77f564f74feb8c38efe95a.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -1, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 9adaa71c9cb9d5dccb8caf67a4a3d1038db92785769dd2ce6e0e6616de90f9c2.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 13 1]

-- Cycle fingerprint 9b0a682d5f8c894fdf587b1cfe3308fd80a43bc7784c7b2e8350dd39f560af1a.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 9d5b60e6de2f6ec6ff9a65606d20ab200dea8d3ced480d8d0e679c004d39dccc.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![-1, 0, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint 9df9768de6ae9cbc5d869c68b104852abc2e0320b8dc35c89960cf08f2b26668.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 9f590a902500b504d686e14d183ceeaf74e198bff9e7dcffe0004d2aca68b80f.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint a301fa5b19d44dc5375d0979ecc3e9f91774602b18ec20df8baf80f66ab248aa.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint a321d883c6f1e448c2a4ca3d8137da6df654cfba06809c4e37724dc57241bd55.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5]
    constant := ![2, 0, -1, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 2 2]

-- Cycle fingerprint a8a3e3338f9c4de47a9287ea8e40999ab24f2e32b555dc1e4729bcb76027ed9b.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint a9181db7b3c154cfb246cf74f3b0ddc8991c42e11920e155b70b4d1779f27547.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint a9a35ea68b198be849f83931d281c0186472d649528265663906749a48925f2c.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00146 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint ab43e25cd1edc8e6f93e3d3a0e9d46cad4a8064265a61caaedfe90c364832317.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint acb3ea0e3ad98c068db0531f06facc6adaad0557254fbd487cb31e5d502501db.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 32 0]

-- Cycle fingerprint ad4b20b3b97292105c2ba839ee705e01bcdaa56235c5e83152e1151788882040.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint ad72924072111d9f95e673edcdc05dcae8b34e6f7cbb9db50f34d92729cd50f8.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint ae2d9a52d96f13d3414877440874384eb621030bd184d3437c25e972f0c1ce5b.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 31 0]

-- Cycle fingerprint b04e2abc511bef3ae694e624a96275ce62c0bd092f7d3276ec253052b1e215f9.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .zero, .theta 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaLower 2, .thetaUpper 6, .gapUpper 6 0, .triangle 13 1, .triangle 12 0, .triangle 31 0]

-- Cycle fingerprint b108706efa022c33903484001395cb74950235563e052808166b4b18facabde9.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b38f29dd9e1898d093d9ab40dcc1f11cf821507190753c01d38565be117a9249.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 2, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b4cbe103184cf146c6037dc54fbb5839207f85f150bae554bd95f6dec95d379a.
def localCycle00155 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint b570f1b8fd5a1ed8e9f109da801ab49664e12e3dc4539732002dfb16a31225fd.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint b80705c75fff0e7c072f1b6def3190fdd6161ee1b635f94c850c3fcd1f933f01.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2]

-- Cycle fingerprint b9126e1e22dd4b19ffd5a5e270113579c3c4cf661a323cd4d069c00b00ccb60a.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint bc78ffa9a9fc7a24fa6874d43cce95653ebd2e3e823aaacbf26f42611c54c18f.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6]
    constant := ![-1, 0, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 11 0, .gapLower 0 4, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0]

-- Cycle fingerprint bcb841f2910e19fbfcd47cfd188a37a53ea3b3b5b60b4957e9d96b22ff7bab72.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint bcedfed5dc72315041535a2bd7b279d13ecdea59a6fe1482357b94c6272cca61.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint bfefb617506baafceb576026eafe17f592309dce89b44fb3eed34abe05a9578f.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c02cabdbf0f3b23aaa65407d11985f6e0ef88b082e8cf57e3993e839cbdcde48.
def localCycle00163 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .gapUpper 2 0]

-- Cycle fingerprint c0d2757201d2fefef7bfe4e00912135158fe9bc0d8c296e673b73de6dc13fece.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint c180f61cd083c16182e4632c0d3af72530d9ff715a4ce39e0a015636b01271ff.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint c1c264b45666afa7f9b09c30529a7394f9167076a97378d8c1836990b9affbb3.
def localCycle00166 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c38a1d6466e58dcc1dcee93b5ef3eda3646daeb180c124e49f356bcfc4bc6941.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c61f8ba8f79fb793e26331b8c62a433dab0551205471feda04101eef4f6121df.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .gapLower 5 0]

-- Cycle fingerprint c82d056eda0720f32cf7fcb93b85c6cf5fab6d0d9ad33920eca8b6e699834269.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c97d421e6c87b89dc0b81512cff9338f83b4e1f0d5077ab174cb5ec6aca1e013.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ca6364a95dc1d26ccc2928022cffcc1272c363696e123e3d831a1950ceb5d826.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .triangle 21 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint caf42417d449d58befc1b14a8dff623b59bfe86e1d52dbef817b1cbf2c7cfe6d.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint cb80f22d5191d71bd577c823061900a9717f2a7580863e4009f34b18df29bb3c.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0]

-- Cycle fingerprint cd4a8c54c7da74d8985fdcf56e7f9f70396c7b3ae929818c84f02f784a6ec12d.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint ce01af5505c4fd1f5efd916cb9a825a76eaba50313a429c550133dc8a3d95f4f.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 2]

-- Cycle fingerprint ce9b2a0495333b5dedfab43a2ed908d634ecbf8418f1846ebd2235628c28d5aa.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -1, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 13 0, .gapLower 0 2, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint cf326e64ed178474ecfa7db611b52057db7c27af7a411d169b9e2eab86df595a.
def localCycle00177 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-1, 0, -1, 0, -2, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 23 0, .triangle 34 1, .triangle 12 0, .gapLower 0 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint cfa727e5947f852e0d436752b2f1d413a60c166255cd06ec0e5798e2b461c8e2.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint cfd357927e5c69f89e3e85a709292eb6d0dea901c00b5d0ef5c9eec5ca84dc01.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint d09569c559c74beeb0986e69c472adcd2d83aea58eb797bfdb2b8b27ddf429ad.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -1, -1, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 13 0, .gapLower 0 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint d0d1dcc4e7426052b0c82aeac1ab16e542f199a080172d938fe83a0fc53cf001.
def localCycle00181 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00182 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d458713f2476c9bc16bcaaecaebfe1294ac2dfdb972d5822d807d8c25c067ad1.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d8e471397c0c2e61f9105b271b0b36238176e25549a0258e1ee13f23c2d5ea6a.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint d9a338befbfe94a459711dc729216c3061caf5a27408388fc3e910ac83ab22b2.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint d9f0103238a38ec4728e117707c07e3cfa9fbc85d96739fef23584049c0071bf.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2]

-- Cycle fingerprint dbfe3b51eb0761a5396081a1181d2e32c39a053654047adb80f2d26d611f1ded.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint dc92a4da6396ae359fa535b0543e924beac723b9423b566f58087426da6fc5f7.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e068f7b9c206da40b80230e1a677c35a878f58e90c674bae924c20a6d691cbc2.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e216c6cea2adbc69fe31bd55f5c87f5f9d6d065d5925fb262cebfdf1387885a9.
def localCycle00190 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-1, 0, -1, 0, -2, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 22 0, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint e4109b744935b982e99ff9bb02ac2adca6eda89db5dcb934f22951d24c8e4800.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e508edc1a82159b3f05b10555e31c00aef4aa99a7f631123344cb648363534f5.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint e659dc187a847c16ec0997e63a8765eea5c3150ddbc2cdb7d268473424291531.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e74c1eab802b66ed7ffac390e03fef04b8bd18bec9abd03671cbd04844c78006.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint e7950f6f8536c1c14ddbb925e5be7216b557ba4106531f621b8f98ae13341af7.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ea62ab71a7a6d383c48a4543736c88abb07e901b7a7a36040e1eb782da434e7d.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint eb4caa3bd63024c2eb7346221f3725d65963053c544d18a277731ca05934afb5.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ecda36d9eeceec91d9dcd3bf751906a85b715a7c2dc5b4f3a7a853a010b1b748.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 23 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint edbe47c92e8318715c1c1359ab0477423e4a27651a9faf442d0b87ef10f58b2e.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 32 0]

-- Cycle fingerprint ee52185d76110cc1a0841282ba08404bb53cd288ee0a34f2ffb4dbb78f2fb61d.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-1, 0, -1, 0, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .triangle 34 1, .triangle 12 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint ee60904ce98f13225cd0123a8d985163fa879d46878086915e4bbf151817eca8.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 4, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 31 0, .gapLower 4 0, .corridorUpper 2 4, .triangle 16 2]

-- Cycle fingerprint ef24384b2a9da96fd81c953497e7c6f3c4fe67e68c926064135903f9cfd05ec7.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f1d6ec30046879e72282fe4b4ecf0fa8eb8086e81042836e31227bc34d33c121.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint f25ce26a44ed03f58b931a3404ceb94b80634ee461f95faa25363844936dc344.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint f40b7fb733b878138da46ff2dcad1188112d2f9fdfe7162a963f2686b10550ad.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f4556e89dc201f3e321165c7bbc208c56a91e8a57da7d33b684e08a44a64885d.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 13 0, .gapLower 0 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint f54665948173455016aa0614f2e0ab34540deb98b080c03647b4438fe943f3b6.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00210 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fa741fcedd11c34c00f0986e0e6c70b98d28c71a1bd748e2495df35dc186a51a.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint fb21f9076743db575fbeff52e51cc6e09bdd094ea489610b002587aa684b54a6.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint fbdc719cf05cdde8c768a9b4d289e5d503619c82c2bc70f9721d86f38be7cb9a.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .theta 6, .theta 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 6]
    constant := ![-2, 0, 3, 0, -3, -1, 0, 2]
    coefficient := ![-1, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .corridorUpper 2 5, .triangle 17 2, .gapLower 1 3, .triangle 4 0, .gapLower 0 1, .gapUpper 2 2]

-- Cycle fingerprint fcd8255100987d3120209be990b896343a2c6b74907d9b579e4adb30ad9e5ec3.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint ff273d2abe6387c4dae86eff71d119012de850faa64aae5c2f215d11447a741b.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, 0, 0, -3, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1]

def library : Library := fun id => if id < 108 then (if id < 54 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 40 then (if id < 33 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)))) else (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))) else (if id < 47 then (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))))))) else (if id < 81 then (if id < 67 then (if id < 60 then (if id < 57 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))))) else (if id < 74 then (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))))) else (if id < 94 then (if id < 87 then (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))))) else (if id < 101 then (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))) else (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))))))) else (if id < 162 then (if id < 135 then (if id < 121 then (if id < 114 then (if id < 111 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)))) else (if id < 117 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))))) else (if id < 128 then (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))))) else (if id < 148 then (if id < 141 then (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 155 then (if id < 151 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))))) else (if id < 189 then (if id < 175 then (if id < 168 then (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))) else (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 182 then (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))))) else (if id < 202 then (if id < 195 then (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))) else (if id < 198 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))))) else (if id < 209 then (if id < 205 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))) else (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)))) else (if id < 212 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))) else (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 115 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13440)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 143 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13441)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 143 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13442)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 110 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13443)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 187 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13444)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13445)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 115 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13446)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 110 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13447)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 168 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13448)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 55 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13449)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 168 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13450)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 4, 1, 2]], proof := .tail 66 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13451)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13452)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 115 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13453)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 90 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13454)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .low (![44, 62, 25, 117, 146, 23, 77, 56, 37, 165, 161, 189, 76, 106, 32, 65, 155, 59, 13, 72, 189, 140, 125, 38, 156, 52, 121, 102]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13455)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low (![44, 123, 25, 117, 172, 194, 0, 186, 37, 165, 149, 8, 76, 106, 32, 31, 155, 59, 13, 72, 8, 140, 125, 38, 156, 101, 121, 183]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13456)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![44, 123, 25, 117, 203, 92, 77, 186, 37, 165, 149, 3, 76, 106, 32, 31, 155, 59, 13, 72, 39, 140, 125, 38, 156, 22, 121, 81]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13457)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 4, 2]], proof := .tail 48 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13458)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 4, 2]], proof := .tail 88 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13459)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 4, 2]], proof := .tail 88 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13460)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 88 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13461)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 4, 1, 2]], proof := .tail 166 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13462)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 4, 1, 2]], proof := .tail 124 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13463)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 124 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13464)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 0, 1, 2]], proof := .tail 210 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13465)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 210 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13466)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 210 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13467)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 0, 2]], proof := .tail 87 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13468)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 6 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13469)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 91 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13470)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 2, 0]], proof := .tail 4 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13471)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13472)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 129 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13473)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13474)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13475)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13476)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 104 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13477)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 143 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13478)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 78 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13479)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 113 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13480)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 34 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13481)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 57 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13482)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 78 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13483)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 113 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13484)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 171 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13485)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 47 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13486)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 16 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13487)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 57 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13488)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 95 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13489)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 113 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13490)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 4, 2], ![3, 0, 1, 5, 4, 2]], proof := .tail 184 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13491)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 1, 4, 2]], proof := .tail 185 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13492)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 1, 4, 2]], proof := .tail 185 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13493)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 4, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 64 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13494)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 4, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 204 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13495)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 204 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13496)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 204 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13497)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 196 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13498)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 196 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13499)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 127 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13500)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 60 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13501)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 60 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13502)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 127 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13503)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13504)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13505)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 4, 5, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 82 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13506)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13507)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13508)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 4, 5, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 7 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13509)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 133 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13510)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 138 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13511)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 212 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13512)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 119 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13513)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 126 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13514)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 144 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13515)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 53 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13516)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 33 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13517)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 119 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13518)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13519)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 4, 5, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![0, 3, 5, 4, 1, 2]], proof := .tail 28 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13520)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 126 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13521)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 144 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13522)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 53 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13523)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .low (![67, 201, 71, 162, 103, 83, 98, 177, 205, 141, 193, 130, 135, 24, 108, 145, 116, 118, 188, 36, 153, 214, 151, 30, 99, 199, 12, 107]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13524)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 53 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13525)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13526)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 4, 5, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![3, 0, 5, 4, 1, 2]], proof := .tail 192 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13527)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 105 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13528)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 4, 6, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 0, 4, 1, 2]], proof := .low (![79, 49, 21, 213, 182, 69, 180, 190, 122, 51, 158, 40, 176, 197, 20, 73, 116, 208, 18, 175, 85, 61, 200, 211, 50, 112, 134, 63]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13529)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 170 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13530)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 170 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13531)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 6, 4, 5, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 58 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13532)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 170 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13533)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 170 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13534)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 6, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 58 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13535)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 1, 2, 0]], proof := .tail 170 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13536)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 170 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13537)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 58 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13538)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 74 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13539)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 74 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13540)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 2, 1, 4, 5, 3], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 70 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13541)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 152 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13542)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 159 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13543)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 9 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13544)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 119 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13545)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 209 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13546)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 42 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13547)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 119 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13548)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 120 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13549)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 119 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13550)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 5, 4, 3, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13551)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![46, 206, 71, 80, 173, 26, 17, 179, 205, 147, 139, 41, 76, 137, 142, 14, 68, 59, 45, 139, 93, 97, 207, 150, 128, 100, 111, 75]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13552)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 42 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13553)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 119 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13554)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 120 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13555)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 119 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13556)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 5, 4, 6, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13557)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .low (![5, 84, 71, 215, 148, 19, 178, 157, 205, 141, 29, 131, 76, 24, 108, 96, 109, 59, 188, 36, 131, 214, 43, 164, 99, 136, 12, 160]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13558)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 119 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13559)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 5, 6, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 4, 0, 5, 1, 2]], proof := .tail 167 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13560)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 0, 1, 2]], proof := .tail 1 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13561)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 174 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13562)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .low (![163, 132, 21, 213, 202, 195, 77, 54, 122, 51, 114, 198, 76, 197, 20, 94, 109, 59, 18, 175, 198, 61, 15, 89, 50, 2, 134, 35]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13563)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 1, 6, 5, 4, 3], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 169 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13564)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 191 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13565)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 181 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13566)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 1, 5, 4, 3], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 181 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13567)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13440 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13440 ≤ id.val) (hhigh : id.val < 13568) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13440)) = true := by
  let j : Fin 128 := ⟨id.val - 13440, by omega⟩
  have hsum : 13440 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13440 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard105
