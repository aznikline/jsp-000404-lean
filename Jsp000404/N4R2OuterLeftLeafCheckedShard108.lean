import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard108
open N4R2OuterLeftReplay

-- Cycle fingerprint 0050fb45e97e055d1c524fb9b932aacbb465d58ec800a5303b828834f49dd803.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 01815c9343849ddc926dba5bd372cf3eff6f77ca48c87d1eec60c49cae8f93b3.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 03644e78535b967042b2373ee831999a4b71c7c7aa37c9417039d23d94731ff8.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 04e5ffb8db778176ac49c0d703adc7d602ee11cb59d1518fc3581f7ca8e717ab.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 05c652044a6295a45ba4c07dcd2b91739ae51211dbf51fdc2c269755d2b0033f.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0]

-- Cycle fingerprint 05ec3f316003145098a9f40f63ab5cac712fcdc9b00ba42f427a4ab28fc0d3f7.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 05fe24d6411965ce3d4564eea587388e95370666d44bb187ec1662e8a29c15dc.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 20 1, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 0775d6d0e4afbd589ec92122a248f4cc0d90caa8e69131c7826437cc1be6ddcb.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 082bdd9f9c6478bf59961a00d049eeb82e00ae0ff42b1bea8e4a76c2f3293f74.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 086b6cb9e1d050098db2afa819930e68ddeb3df768ab7c8f3d527e4524be7b79.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 0ca5e6a8b40b1d218668c685e83e9f49e8cd7fa270515fb19a994adc29183dbd.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 3 0]

-- Cycle fingerprint 0d712e256ab546a28201d1f57ca0a8b0161f279086d38c07d3546cfda02797af.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0dd982884866f174f4465874232a2ee6af2ada317cc7cc14eed9e07b4346718a.
def localCycle00012 : Cycle where
  length := 14
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 0f68012e26af46704dc8ef74b1cec86a5d446515d27672c4474575dbfb6191b8.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 0f87897d087f448d6c4b210bb499552ac57044ca0fec4941f87eaaa9242c7c91.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 0fcee8c51ded943b64c1e42788ff6e52309b1e9bcb5568f9ac98c0a1b6a2da47.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 0ff47fb6fbd0c76bcad82d98dc7ebac1c9f4b22a0d5503a63bce4cccd4f913c6.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .triangle 16 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 133f6d6bf9a59d766d291fdb0e8cab0d6af1c0f2a2f25696380b39acbf838ff0.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 179e1081a76b766599c91274765e37486717b09ed0592c2c833a60119e2becfa.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .triangle 24 1, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 18fc9284ada0cfbb75f672c4760fe099480095e339ade520d4c75827eef5b9e0.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -2, -2, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 1fcf7e8bb913c0475a0bfbb71cc01cfd54ea3640e9cdbf7478e86c7477a7d281.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 228327da454d5cf47acaf100031cefb00e876a738535fe479e0596b212a34246.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 2, .triangle 3 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 229ad49372c98794c1f2de1ac7708fd5475870107a4fbbc07c462c4fd6938ca1.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 23769e126398dfec17288c55cedeefffce4cce198a775a197f83c411c736261f.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 25c08db3adfc854449b0a3de645417f12b4463a11dbd53cea2c4012c9161dae5.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 269a7412925f34caf7fdfc63e477fe45a4f43a73a24ec93fdd0dc5c94c359c3b.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint 27325300a1a6b6da15fbbc8a59dc028b991a583569df379716f21915bc429e87.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2adfcbf543537733c8af2e8e9eb45903b4957788491ed72275f3748fcad02734.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 2bdb8e1a540cb3216a25cac861111867e4aa8de69c10949a295058f265089b4c.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint 2d12598f4ed7e8a648aedcf6ad1b6f88019008673ae32c7ecc69473db0c76457.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 2d49a5e2a090b9bebc690befcdfc990baf2b2a4dc65fc6e714b2802a2e7329fc.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -3, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 2e73c3d8b7ced30d4e8845263ac724517bf703535d4d945f22f72b84ab586add.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 3, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint 2f04845830f104d2a51975511c183df4419da893219ff4864aac4a348710be52.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 4 0]

-- Cycle fingerprint 32892d1311fc20b3ff15853c0ccf03df4306a97be68959636695719be29f98bf.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint 33a7e7728d87f840a37b3bfd2f44bd76c63169ac519586e93314e309b1db6dee.
def localCycle00034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 355f1b47bfab238b2008b134514e0ad7bc097dba92a6a6455866f0337b50075c.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint 362b2e2b405e4fd486a1eedb5b3aacf93eb2dd58494c5449fd7fa5c7e480d918.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 38c9b624e91d37310db092a955ed7ed6072aa0b4008fdb05904a3bff3e0c80b2.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 3c04b66c9c4be91ad07dbec327cf9810bed1393d092880dd3b5a7da0aa1ff84b.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3d04b1ed817b0c0b2696cbdc5c8010c18d93e28455265466ea8cbd5283c72ceb.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 3 6, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, -1, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .gapLower 3 6, .triangle 21 0, .triangle 20 2]

-- Cycle fingerprint 3d68f0d0a5351e591c2a9d9e507208425fb3f8c28c34e0960c6922c47ec43d4f.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 3f432680ded87c372f2c0845cae002d9f705951d7d983b4e15168e19cc08674a.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3fd4bd3a807f431d1a528fcdabc4376e42a0017c0e366ac2128fe73cc0abf190.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 40a660c721162684db0a217628f69b6d3f654b65efcaa15706885f947b484a74.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint 40b57a6bc79e820d1e290fa5f869bbee9c9e8302b84bf61c45bdfcd376275929.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -2, -1, 4, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2, .triangle 24 2]

-- Cycle fingerprint 422d3a024a932a3585a7867fe6cfadee07434ecd24230f002379ad6c3d1d667d.
def localCycle00045 : Cycle where
  length := 15
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 4250b8a724a65d890bfa38b787c26d4e8f81171ffa360f6d900f82d0c9a67139.
def localCycle00046 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 4327209e9e33a0a4cfa66806f7dff29c896872a64dea5f1acd63ad35049cb135.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 43e0005f8283369271aae40a283ff0d05bdda56fbbb8167ddd9b33a9934fafb3.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 43f983936d5a54bec9284aae3a9a86abe2ae6959d0c20b7e97a160652b4c26a6.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 441d65d6600fec02a3332b268b848b9ccba8fdcec05b468f016db38997dd9b7f.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -3, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint 4508abc04583f4e1d362989f8188f6e5a4e9556a6b0eb8f6986431a9250d357d.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 48a5d2acb034607aa7be52f6b18a431d3390082ea97afa2d51aace04cfed3e25.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 4a15c82e8fd41f25e550bb1971d052e672ace040b4d99a100f46f8688d446398.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 1 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 4a2f0d29fe4f700490e1467fdeaed6a1d4fb5f54904619a47cfd8a257f36c077.
def localCycle00054 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, 0, -2, -1, 0, 0, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 0, .triangle 15 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 4b5240dfdc90146fec175f4f9c7be93b35edc25fb84b4519e9d63f7251510708.
def localCycle00055 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4cb9ffa84a53cc6660454bfecf3eaa34e58b621fb5600d40533b0f61960284a2.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -2, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint 4de87554a8c034b736b6d6c49ddc4ee20805ededc9d631fd2906017a0bfbd5ac.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 23 1, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 4fb845a04a2329dbcb6cb9e549ff61067bd06cbea66eb0aa56249613e4948dc7.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .gapLower 1 4]

-- Cycle fingerprint 4fc2b5ca447f80e7b195c0008d1f4bfafcb35056f2f206ec92b08773535512fb.
def localCycle00059 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 50add3b672832f8c754b1cd864e2b9f78c9bd00dd6623cae3a1f4b74e7275431.
def localCycle00060 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint 50cf6dd84d385178db46330a31f49dd135209aecc4fefc657110044bb0a0e190.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 52d76e71752c463d36dffa8fefdece3c9c4b88bd9a800c07fdc3444df4c593fb.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 5388b54c0d4a3e3f3769968b0ff1d1a4085fce55f1f43bac527742cbfb0d7060.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 541959b651dce2cac59d32264e2ed8c289a9d78f6d38dff427629133868e9948.
def localCycle00064 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 544354ffd54109f5e0a1ce78f09bfd41b871d4df18ba6d604bf0f00f06a1712f.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5534f7040130cf469a0c1608137ed5d7c2e8d1a76f4354d09071d1ca0d105ee6.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 57944357a104131606cd9ff494b1d15418a7d9d5af5ff9c8f96201fbb85b6cc7.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1]

-- Cycle fingerprint 58409fbf5243d450f63cbedbd4ae2b8034149fe1fde87442314b5d470372e826.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 5980fced304252d9b9475ef30151c1729f18f7a88d33fd3a92bb0d4387657ab9.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 23 1, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 59a0387085d3b32404f477bbd710673b5b62b44280e928c2d6214c211b143163.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 1 3, .triangle 18 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5a06c1c36b09fde9608507628d14086a02db0613a7c812fe1e9ad0e04b80ab6f.
def localCycle00071 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 5a16a4a4b288486ecc8e8cb20cb2d44fc8246c433119b429907fb1a5e619373e.
def localCycle00072 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 4 0, .triangle 18 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 5bfb6315ba8b22306b5c8ae71c6323e89ff27d578d02cf10279e526ed1caad3a.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 5c54e804b36e25af2c93538a32afaafb78d969318b5be01defc7588c0467e065.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 5f38b96c62237de04ba6fb96fa7c79e4867cfbfa29ea67afdcac787c3a7bc6d2.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 5ff259279d59e1c6dd5c828d724d84ee68732752205ed17d7eaa03c500740c66.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 610900255f9988d35c5a8f5524208727b4a8bc12a5360a40ecc22941eda3ca4c.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 6282cecc83eeade85df1adc15338fe11556f60451aee307d55816192d315cdc8.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 642114c7bc6bca46142981abf44b75296b77746e9c356b7f29b252d606326fdc.
def localCycle00079 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 698406e9fb38ff1764bc2795fe0433b0a6827e390158e81dc834adf315776ef5.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint 6b25b5896875e05d68eac5e2fd104aeb443568d6a54198aac64e9eb45a394743.
def localCycle00081 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 6b85639014c61da25e1838f8476148890f85ebc2c037c79313a3a8f4ab8d2dff.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, -1, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 6dd1644719bd2cb952f7826fc5c4d7e2e828ead379697be08ef92ddd4e6763ba.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 701672529b6f05ac528d89b400de6aaa8b40d1b233441d2360554953d5b59176.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 70a5ca8f23ee433a09fc88d6ce0a7f9148c06987be40cd3ba4fb9d7f0abd480a.
def localCycle00085 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7333399dd15ac730eebb28bd88b5f97acb1ed9990bccf19e77af856f0f7b0341.
def localCycle00086 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 76afb63733e98b0111da7ee501a618e7fdf3ee588a01cebb0a975261d5e5b4c6.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 76ddbbbee0857c27d61e30f7fcf9d11babcc4c20b858f729ad5ceb43ef85294e.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint 787a84f97d70c391fcdf2c73274f69de26e9f7f1a6213ec340059feb37c4a6fc.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 78b69b84a41dacef7b9cf4a939f8e460063e25dcca7fda08270cb7612c8a0367.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 20 1, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 78b97148da7304cc3cd8a8fe60734b7cc33774550687a03171e7effae088a6a6.
def localCycle00091 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7a116387c4ee8f5b88e237846732e6160a094fd4f65e14f3f61a1967e23f6b3b.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 7d467993c1d63f80df3beadbeaaa527eb33fe8af19556b69785a8fb624a3fe8a.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 7ed3ce10276691dc5896154957ce20c10497a4d22ac112ec6be0e23e31d8ce28.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 815ed749b0df718f5061cc2f8c71b99f9a8a8ebb0618f2e916f7520234597579.
def localCycle00095 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 83830c4be922eb2e35e57869391c077a75871b46e610661642f6de3440f6894a.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 84e49a9381dae6a5254ea057f5fe920a1b65e6f39b1a5fa7831328b6eea1cf68.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 85aadf5970a4413006b3a58334bce56b9fc4a8ee922eda09d49cf756dbd1688d.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 876c45d213a6e0255f10d5325e49311ad550af28261d085b3099c34ac8812a73.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 88ec953cc1a6238a86f260ca778d2be1e6f4747f68086da72843560e38bd210e.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint 89c707f3daaaadff6b572055f4ee0f50e9fd32206353a6e0c38bcf9c611fce9b.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 8aa7cff7dffa148b3c3497f9266a4faaeeb9fe6f30ffd415244c5046356f7be5.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 8cd0fb99c4fc56001eeb8a7bd695081f7b7dea70fca8e7d20e168322d049cc0d.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 8f59bde9be21ce9f668f7c9c806a0720464e8d47a854bbeff0ba50f5f0f6cc83.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 8fadfc2998849cd72a97133556a71d8b98a891ac6f74d24d81da16ca52842a2b.
def localCycle00105 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 917ec7dd044464bfcbb0d436b0172e1c44e0d3249cfdc218c07d56f6cb04d08b.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 92396de8490437000036bf33ada89424e238025c1cc1a521bcc0127e55311a73.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 926f47681afdcdb1257f0a2d64fd7abd73b6b15bc409dc123d93646d330ebb84.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 95a55e7d6e6179e54a80d87538427135fcc37a19bd49acfa5b00cd41968c75bb.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 96d5640f0b9eaa1e1d94e9e5f2fe07d68387608502bc53aee1d7aecb696b2d53.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 997af66c753ff7eb19c67328c22149ef8d52cf28a584bc273856437eae3132e3.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 9a23265b86fa2c2f252f498c10c4bb54192f970ac097faf4fd21ab9f36eb765f.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9b2139cdc10fcf80630f9c572c631ea77c2a85f5f3aceaf577555dd7939a0998.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 9ba77e3c5fa574127c9b903bd82e0a805c550c84620b8bbab9bed3dfd7bc4136.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6]
    constant := ![-3, -1, 0, -1, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2]

-- Cycle fingerprint 9c17e928d3dce5f26f32e698a2fca6ee0d4a882a7a62ba2ae69e711ea191ee18.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 9cea2578e4894b5eb01c454cabf57306893b371ffc99f97567e1e34c7c675b7b.
def localCycle00116 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9dd1d6fbb5fee8b16adaa4d5260881768692e8d262c8434f396becfdce8c8cd9.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 2, .gapLower 1 3, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 9ddafbd297830ab0998cf384c51f6fb7505f5af2e0fb6362d279b07aa505257f.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 9ec7ff8c4b5f8b654768556cbb69257f78bc179062fe2baa73ada85a9cef07b6.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .gapLower 5 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a071305e7cd58c3ef7bb52390c08a5e3012a0463caa70f532c0afd81e6bcc98c.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint a15eaaa469afd6c50a6df89e401d2ddd5f027165bf56918b704cb43e4a47584d.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint a347f8c11442fe8f58d435b24155340b3fb791edf625b193a45f293243edb505.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint a6682e0c652ddede38859b155eeab1f3ad7d9678a371b9a0918e0795e9eb740e.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint a77122489165686c8444a93240c7fa1b855ea8220b08c7f5e0551b25ff1b4762.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a84ce24721cbec1162ed19d73bdd6d57b23faa4e6777634e38c49979f4f4a1ea.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint a940eecde8d9045ddc327a4dc256e92bd7bcb0144ebf5b073a735d977bb9e78d.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 24 1]

-- Cycle fingerprint a9a52e7ee23ce01aeb4143411553c42095a7de22b7c604c8953c77b3ee0f22e8.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint aa6c30db13febba774917ca991a5fbce2762f38cc9a7872313c66bc2f56224c4.
def localCycle00128 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, -2, -1, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint adcb94a77c288c216b0092f6fa2c94cffc70c6da1e440ae82e8c3275de1c05d9.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 3, .triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint b11858dd374569f69bf8c5633fcb51569e35e3077dfbefce3836af40df42a983.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, 0, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint b2ffda470578d9c5a16f43329f125ff3a913c939a50146f194d33b842b351189.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .triangle 21 1, .triangle 32 1]

-- Cycle fingerprint b367b52287a64a090cf6c3f228bfdc7f4da5b045a076095da14e5d9854f1fb33.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint b4f44b384f5687467dca9851b8ca4a5b5459ff02ff376ede73567532088346ac.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b6fdedebbb2f0cb10b96350a3a76f6d99f8e589b3a22d35f3edb0d068b4f948c.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4]

-- Cycle fingerprint b8680b53ad40c8649052a8da2d92d75e0768028b76f2fc5e4d78e3af51e90fa7.
def localCycle00135 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, 0, -2, -1, -2, 0, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 0, .triangle 15 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint b883788984969e568091417a549a0d8ad58fcd94fe2bf6e1f64c60ebbf32a7bf.
def localCycle00136 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint b8c074d2d55ed1f76ac65535d5e33ca0bb4f94d5505dfd90e0a28bea67fed701.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint b9b4be8cb76edca19f09b78d860049bcb4369293ce628b4f3234b4e2900a6516.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint ba386cda0b640803c9698e721dbc9d2009049221279dd1984d7d133160564a13.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint bb18e83170f6c01659564f352584d3e617d7131e9f590e44d1cd7e12f6833444.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint bc76827a5de59f9b9b877977469e4c67464e8d4b0f77f40bf1326118aa6db13f.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint be0a82b69c08539aff4fcfb581d757e40f9293c340ba98ce143d2bca39c0c8d1.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint be19141881aec331a6450e5049700a20d071b02e48245c745b67d05bd0526d10.
def localCycle00143 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint c02205166267b91ecc320052b70c8ef1cb7b0215d80d961424c29caf9a810d6e.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 2, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint c1dbb0172032af5b298072848b4622fe9afa04864b56073ed59f268c402509e2.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c396da7a131401778f0648092ce6f82ba39c739ad9be5fd63885ee7413d71493.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint c48fef0c1baddb818747f4c1443cd57e875480ec5d07fa6983f10c7d4d39d274.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint c51e4ef90e28979bc08d60fedd9a055e3143f8883812a4526fb62523fef8bc14.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c609efae3ec9243fa72a08006006ec312aad5cb29205673b3dc433cdb3b6c361.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -2, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint c86cb035069d6ff12461e6144853da9c3a6a46d8d7b93f3e9892ad83b227e4d1.
def localCycle00150 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint cba78a301c0502cf34ff4e72cc5d3acab71efae43ec74bbabd9362650c204f8f.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint cc7d06a41d4b0640fcf04fb6cb87bb3c5b7497842aa54c8b4a33ef278f38c30d.
def localCycle00152 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint cf84fd7b3d269676cbc5a455da5c3e9fba0e6cb72ac2d5a67bde1689af530ece.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint cfe9b85beccbc8c27a3f32fa2ea29daae457186ee2e3ff51e91b63e133afd28e.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 21 1, .triangle 32 1]

-- Cycle fingerprint d0cfad5501e385317ea06c12337f91fcf67c3e9ed60712d7041158f5b7259d1e.
def localCycle00155 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d28998787a81478ce58367b10577f024b69874c3862debbff977b3e5154c6613.
def localCycle00156 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d458713f2476c9bc16bcaaecaebfe1294ac2dfdb972d5822d807d8c25c067ad1.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d46d6c90c4f19d8a07c5dcfdc5affe43a61737407c6027591d78216b1df39a07.
def localCycle00158 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint d480eed84a15e4c95651e3e6d4c8cfdf6c9b51c3ea1732264a02c9754a27e3af.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint d4b58001152a18b88fb8e2304bdfc14471de69ff3b8a9dde228d94f6403df454.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 2, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint dcfe43e06fed21040510b467a3037169467f18b454f3ec8e985b7e32b608cf78.
def localCycle00161 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 24 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dd33cb72725059c92e07d5a0f6acd061fb4192a2bc6ad00c950c7eeabdd43e38.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0]

-- Cycle fingerprint ddbaab1fcdc721e1ea0e52189af33710d10ab99994cb1914b869cf8d82ecfbf4.
def localCycle00163 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint dfc9d0b331116f990c97dd1a1e0a0c6fa62951b37937cf4be200b713e1163815.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint e0871944bec90876eec9469180c9b271487078a7f2326487a3d0d3a850628435.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e09dfe7d19b6a611626e779281bf86fe98c335d2edd9fc2ce4f5303160b61b88.
def localCycle00166 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 4, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint e2083637d233d85699840e63921837797a77d00038f55b73030139b46a5c58e4.
def localCycle00167 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint e2eb655a919b35ce7fb6642288d90e68a716499b64a2c011dab5e7d11da3874e.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e3a90003493a77c8d91de6e3ccec2f8ae349e3679bb15ab4d1d4ca839f4a854a.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e5f3549788ee046ffdda826e1dff1bebe54a0c28e08f382e1291e34b2575d385.
def localCycle00170 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint e6c4b5536b1a35a3b1dcde2f1b9bcdfae2e760d06bc28fb46583b34d1ce0c884.
def localCycle00171 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 2, .triangle 3 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e74c1eab802b66ed7ffac390e03fef04b8bd18bec9abd03671cbd04844c78006.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint e76914596fa05c092f8400582d417b21df2e6a26309c577f086e09f7cce045ce.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e76c94bb01ddd22e7bb9f382003ca4f887ac210404f0369a5be560d8a68577a0.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint e77bd302597e42930b5652e5f0ab409ad2e4cde579ecb195bee5dddd5092e5e0.
def localCycle00175 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 3, .corridorLower 1 6]

-- Cycle fingerprint e7ee1213fc8ff51571730fe69fb4d91cb33112cc00f9c51e776326bc734e5743.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e9967199fbe3a2eb954dbc0585569e6f4f91366ab91b8f108e78143659c82337.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 21 1, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint eae06af19666b1de74b766a9e2285011eec4596ce1ce4637f1c7236cdf50fff3.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ed7ea719443df962abcb39c08017b38c5a5e4f8658a49c6d481605718668bf85.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![-1, -1, -1, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint ee5cad383689aa68a84d2dc9c1b45eca88942086db06f1453048f06f55ccb8ab.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint ef4b56bd64c803f00d51ef09f8101beb94697310507a42f261d3ab3f31db37f5.
def localCycle00182 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint f0569809ac61d5171e4c41a6c3356e0fc70c263fd756e6e15214f092c77fb436.
def localCycle00183 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f07e5346e015d136a3bd60464e6c8f303ff8655097d446924d562256288fd8cb.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint f09043286508c9dfa045a578b9827ba4c7337e1ed04c51e19157ca8ba802bb22.
def localCycle00185 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint f1c14849192ab82ec6efdb0464a3fdb67e8a2e1866d68a70eb4f3f9083fdac3f.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 23 1, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint f25a12ba60c08f5fba25b1e9485cef799585f265fcbee29cdbb5daecdcfff41a.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, -1, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint f42d7776387796d35a50d88a2a007c84afa5aa929564620272e34e8d1f10c52c.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint f4a5d2270ffeb17c15275bef0f148d71c4aa3bfb1ab0448cdf6fc72de311dbc8.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00190 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fb7add72e457e0b0bf0ad7e476c0298f7d31fae7cbad17f2a3a7076bdfa02731.
def localCycle00191 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 3, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint fbe867e5e8d6a2dc0203b81318fb4f122377eb444f29e8edd689dd024ac7e1e0.
def localCycle00192 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6]
    constant := ![-2, -2, -1, -1, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint fc6f12efa8bda9b3ed2f8b977cb2317bed07d90a050a050278573298c371aa78.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint fd39d9b33ddf68f3b88a1a7b2565b0bba046aec3598a8927fa8248d121ec6698.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fe570344e9f543fffcc851f1db3de4eaebc3c045eb842bdf531f3cd9a32d82bd.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 21 1]

-- Cycle fingerprint ff8db9b7608dfd9d49cd0753e55a3de850eb7ebc410ad32da781998916423fbb.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

def library : Library := fun id => if id < 98 then (if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 73 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))))) else (if id < 85 then (if id < 79 then (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))))) else (if id < 91 then (if id < 88 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))))))) else (if id < 147 then (if id < 122 then (if id < 110 then (if id < 104 then (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 107 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))))) else (if id < 116 then (if id < 113 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))))) else (if id < 134 then (if id < 128 then (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))))) else (if id < 140 then (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))))))) else (if id < 172 then (if id < 159 then (if id < 153 then (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 165 then (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))))) else (if id < 184 then (if id < 178 then (if id < 175 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)))) else (if id < 181 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))))) else (if id < 190 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 110 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13824)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 98 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13825)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 103 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13826)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 142 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13827)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 46 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13828)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 168 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13829)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 24 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13830)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 104 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13831)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 0, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 42 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13832)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 24 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13833)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 104 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13834)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 78 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13835)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 91 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13836)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 1, 0, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 183 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13837)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 1, 0, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 3 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13838)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 111 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13839)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 111 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13840)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 6, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 138 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13841)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 2, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 68 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13842)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 145 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13843)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 76 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13844)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 62 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13845)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 2, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 83 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13846)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 147 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13847)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 189 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13848)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 6, 4, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 155 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13849)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 6, 2, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 0 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13850)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 6, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 148 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13851)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 6, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 83 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13852)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 196 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13853)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 45 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13854)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 189 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13855)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 116 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13856)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 6, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 66 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13857)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13858)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 37 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13859)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 6, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 12 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13860)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13861)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 37 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13862)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13863)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 4, 5, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 123 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13864)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 1, 0, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![97, 5, 88, 39, 30, 166, 195, 93, 121, 56, 54, 53, 182, 38, 65, 169, 59, 163, 194, 135, 107, 185, 19, 128, 126, 192, 178, 51]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13865)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 85 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13866)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 127 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13867)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 77 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13868)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 58 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13869)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 160 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13870)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 141 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13871)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 15 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13872)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 144 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13873)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![180, 164, 21, 117, 140, 63, 143, 61, 171, 56, 191, 96, 34, 165, 1, 10, 187, 71, 109, 174, 167, 150, 80, 132, 18, 181, 43, 92]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13874)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 22 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13875)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 5, 6, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 15 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13876)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .tail 17 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13877)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 4, 1, 6, 5, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low (![48, 164, 49, 114, 33, 172, 143, 61, 179, 149, 31, 7, 34, 23, 44, 113, 7, 71, 29, 125, 75, 150, 137, 184, 108, 35, 87, 157]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13878)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 4, 1, 6, 5, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![48, 164, 49, 114, 33, 102, 143, 61, 179, 149, 31, 188, 34, 23, 44, 113, 82, 71, 29, 125, 75, 150, 137, 184, 108, 35, 87, 115]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13879)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 110 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13880)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 4, 2]], proof := .tail 32 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13881)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 4, 2]], proof := .tail 196 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13882)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 5, 6, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 4, 2]], proof := .tail 32 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13883)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 4, 2]], proof := .tail 161 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13884)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 4, 1, 6, 5, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 4, 2]], proof := .tail 99 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13885)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 4, 1, 6, 5, 3], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 99 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13886)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 4, 6, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 1, 0, 2, 4]], proof := .tail 47 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13887)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 4, 6, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 1, 0, 4, 2]], proof := .tail 47 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13888)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 6, 4, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 6, 0, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 1, 4, 0, 2]], proof := .tail 2 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13889)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 6, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13890)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 6, 0, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 1, 4, 2, 0]], proof := .tail 25 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13891)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13892)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13893)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 4, 6, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 4, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 0, 2, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .low (![67, 162, 158, 105, 131, 50, 74, 4, 13, 70, 57, 186, 16, 136, 60, 130, 151, 152, 8, 36, 9, 64, 154, 89, 175, 28, 69, 72]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13894)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 4, 6, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 0, 6, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 190 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13895)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 4, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 6, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 66 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13896)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 6, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13897)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 6, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 37 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13898)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![2, 4, 6, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 6, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 11 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13899)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13900)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 55 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13901)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13902)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 2, 4, 1, 5, 3], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 0, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 123 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13903)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 5, 4, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13904)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 5, 4, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 41 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13905)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 5, 6, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 94 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13906)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 120 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13907)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 193 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13908)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 100 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13909)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 1, 3, 4, 2]], proof := .tail 153 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13910)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 153 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13911)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 6, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 139 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13912)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 122 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13913)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 27 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13914)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 1, 0, 4, 2]], proof := .tail 118 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13915)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 6, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 106 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13916)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 173 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13917)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 5, 4, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 176 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13918)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 0, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 6, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 1, 4, 2, 0]], proof := .tail 112 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13919)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 173 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13920)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 5, 4, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 176 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13921)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13922)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 5, 4, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 81 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13923)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 1, 0, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 156 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13924)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 111 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13925)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 5, 2, 6], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 156 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13926)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 170 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13927)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 146 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13928)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 0, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 40 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13929)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 5, 6, 2], ![0, 3, 1, 4, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 159 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13930)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 5, 6, 2], ![0, 3, 1, 4, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 129 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13931)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 6, 5, 2], ![0, 3, 1, 6, 4, 2], ![0, 3, 1, 5, 4, 2]], proof := .tail 90 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13932)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 0, 6, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 1, 4, 2]], proof := .tail 52 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13933)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 6, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 1, 4, 2]], proof := .tail 6 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13934)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 101 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13935)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 124 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13936)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 1, 0, 4, 2]], proof := .tail 124 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13937)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 6, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 177 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13938)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 14 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13939)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 20 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13940)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 6, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 1, 4, 2, 0]], proof := .tail 177 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13941)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 14 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13942)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 20 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13943)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 73 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13944)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 5, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 1, 0, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 119 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13945)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 1, 0, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13946)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 127 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13947)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 0, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 84 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13948)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 4, 1, 5, 6, 3], ![2, 4, 0, 5, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 0, 5, 2, 6], ![3, 0, 1, 4, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 95 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13949)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 5, 6, 2], ![3, 0, 1, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 134 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13950)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 4, 1, 5, 3, 6], ![2, 4, 0, 5, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 0, 5, 6, 2], ![3, 0, 1, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 129 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13951)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13824 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13824 ≤ id.val) (hhigh : id.val < 13952) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13824)) = true := by
  let j : Fin 128 := ⟨id.val - 13824, by omega⟩
  have hsum : 13824 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13824 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard108
