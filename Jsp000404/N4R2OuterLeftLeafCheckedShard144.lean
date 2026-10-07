import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard144
open N4R2OuterLeftReplay

-- Cycle fingerprint 0046ffb361a815e7ecfce8beb8017c4cf060ec447c3384f8d887bb54ced1edec.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 00931ddc1a9b0708c26ade5213742297ca05369821d68394d26ea2374ed254c6.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 010871b436664871338e81579a366d689bf64186aba03ca7ceab4a544c6a0351.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0357c4c77af11c10cba337f25afe50aba43583470be7d791d463682eb380918c.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 051139db140f41e7fa0d02ee439370ff158dbd2ebd180a16e498e2ce4c5d0433.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0962d478028ec35d93b87893b1de0e2e2d3afe063e673997e65b022df0765098.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 0ad9a5f42187ef687300cd10a156c9b308dd679bc84f5dc040eccbd7d2076dd3.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0c9b5838a82bd96f7f66e827e83418c6aed673ef7c6bece037517d530511f448.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 14 0, .triangle 10 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0e60adc5bb89250b20d63beaf6d9562ba88cd5980decab728ba8786a4cd7b1ce.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0f3478d4e4b2fa91a35970ae3c57d2b7682bf8e10170bf0e218327724b78b2e6.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 0f4c84ac965407fb78bca8937f15171a772e67ca7e5021003b79c7e4ae9bc97d.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 0fee9f081a69f64ceabb88ec3a66bb8cc995365fe5ef1411bfb6269d05a2ea6e.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 13cfc6c1ef424113de01fe3ff46d62830c7d355135bb0e8a33f566d58001e819.
def localCycle00012 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 6]

-- Cycle fingerprint 179db79a378fa52d19352cde52a6b39388e7da4bcfa84451f012a17697608e63.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 2, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint 1abba9554403534f8924d51c559c341aa3e5131d6b453d82674218b4fd1bc6d1.
def localCycle00014 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 1f117bf52b7ed3f2d6241757a731b2f96b844ab33656a9f0fcc8f41b8a59b9a1.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1]

-- Cycle fingerprint 23d0267a2c8ac72fc4551fff48983b53207fac935ebfd863c1f6ac933213d87b.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 3]

-- Cycle fingerprint 2438e615f1b180f8b122c971f4b6df02e2393a03333b17c38fe5382baf099116.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 21 1, .triangle 20 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 25e715e775a1a95a5bd535fe1e74af1e55538afc8dee35069d9ddfcba41db945.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 21 1, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 26cd062244703a593bcae56a2e6e2c74fb536e31a19ebf69eb4a9d9a7e31efa0.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![-1, 0, -1, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint 26ce03176b6ec9298665a169ba589b468a49ae8fee5e310c1781edb5bd5bf9cd.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2980dadfd4f86aeb7fa5e854886f704aa7f86af6078465228e79fc70a70bc8b5.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 2cafdc9de14f99a3252f09165b959479add3596b0de2a68bf84721b0f856127e.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 2d4eb412aa7856db532c224cb14e75ef33e881d34f074867fc8ca54c1aa648d5.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 2f1edcdc3dc8ab20783ea3e35c71fb5a43a92be13dd9f66e779da4288ec7f16d.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6]
    constant := ![-1, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4]

-- Cycle fingerprint 2f744e89db2db3755747ba8006683e46896f0c29c93fa4e546d2d4ac7a97cc1e.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint 3089a323201985934a4ca75883414482f7ed8bf8e189188235b00f999dd73c70.
def localCycle00026 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 3353146901eafe30a5effc34edd49560067f20974ef4a08891536178146d447c.
def localCycle00028 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 35bf52d8030664980d6bf33bf2aee6656cfcba85b1c9b782e7e118d4d661fa82.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 37d91e6a5258579e9769ca4f45d060e115736a64d451a63ad00c1853408b7b61.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 38294a880e1b11c25a73a639fbf596d171e5a50fc28da7f6a83b2fc273a0435f.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .gapLower 1 2]

-- Cycle fingerprint 3902eb46d45aacbf4b41857e09e4e620e557d520ec2ea1f2dff74c2925f69321.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 39de5e975556f42d336ed3e2abc5dc43b0763128af33c7d6b18586e913008c6b.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 0]

-- Cycle fingerprint 3a1a72ef6abc6b92be705aca63dd3ccfcd54d375c00a4f0f9e4308054f17e6ed.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 3ccb934e54896467e46b9c8261b2ad7bf80d74a7aa58236f48951900241a13a8.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![2, -2, 0, 0, -2, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, true, false, false] }
  origin := ![.gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 3dabc0228da0a4293b384e4cac467caae0d1c91d198ee454e196c2849d168d1d.
def localCycle00036 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 437aa3e838b337882e8d7b9804f129a75580de9c45acf8b2bfe3d61418f41629.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .gapLower 6 4, .triangle 27 0, .triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 439aedaa0f8c312dcf109202e49c39e745ae6c597dc53ca6c7b3373b81ba01a7.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 43be29b6a586214cb85283ee8c746682a3f1fc4dcffa72dcb8749de4b45b7b00.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 46c61272d5cce8f6ffcfcc13a6180f28af52238b8f77daba7eeb638a9cfcdba7.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 47d413f18d350b07bae42f7c9cef66df2227e97aa0434883720278dc413d96a3.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 21 1, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 483636f0a76d4062aafcdb40f029ec5a9410def45c36ee2813c1537f08defc11.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 48839692e3f0f134de0fb0740720575afca18116a3acb879f105f18f424f3e27.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 4a5339fb8ee37b9421220a4d3bfdc3928fc69d3bf6ec6892107f9be1332eac6b.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 20 0]

-- Cycle fingerprint 4b119615b57e5bf5f6af585bead6c313c91723d45d91721a40b2ae6c75aa52ea.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 3, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 51a6d8af245decf7a36617585fef1d66c6590511624b6432a3789d488fe81e27.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 5242f85460d691d4597ad8c2345ce0d7a678bfdd2266913d4172e08ef73c754d.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 2, .triangle 10 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 524d6787e997bcb6b4e4af98d011c6c105907801ff471dc9b5d4c86ab69b7d99.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 52c67ac3a0c948b87e1c3042fa4612bfa33b6f087ad9b21aa9dc7a23e7140270.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 540aadb4956f87f18fc8ec3b571cdad4a47c4c331d46ac818746a3ab0e0430ca.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, 0, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 2]

-- Cycle fingerprint 56dc944d7aa8caf8263f9350be182c070d6cebc110e9cf7f6f643dc00f7395df.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 58a8cd432393955cee567042aa2496917e763938438ffcd88f694d68e751f16e.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 58e12d461323eed39d2a1211664693183c78e32f7470f0efd909a83d4727dc28.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 21 1, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 5a13b967c6d5584c7b9029f7a26f93ff67aecada0dccd50a77d78d6aa34b53b7.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 0 3]
    constant := ![-1, -1, 0, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 10 0, .triangle 20 0, .gapLower 1 3, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .triangle 1 2]

-- Cycle fingerprint 5b23e24e95adbb47fcc4e74074e06f7675cab8811a9bbd36651b7e193e433229.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 5e5841eeab8ff635c412d6730a659c5f95b4e2127ed48a5be85dd0ddc99de072.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 5f8834c4f68c62b411f331cedb38787cdfde354daf34c384cb9e16c5ed713b2d.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 602a9bdcd55ef6c93fb79a77f9c1b68f00f15e4033871f26cdb17cd5d8004386.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-3, 0, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint 6085e1046c9fd966b1d76e80ca152dcc6a96995bff45f9dc8786a8326db32567.
def localCycle00059 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 60ad64beacf9e2918ebaf48f92d0f967eb1ef04f243466ba95d073bcd4d286ed.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 619406f95d9cace68d29e28f1f87f34b3cfa28de48a4d453e22755cb82f45e5a.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint 63bb69ab066df65338bd992f39f7173187a4144d614eb0c9e928e647222729b4.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6762cf149237247c2e7c8ba00b0923cf573c933f75f31bad7a38a9df19768c86.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 67c1e1e5b5cbc4d15e7e9aa8cb250ebbfe305dc54df07e4e1b23ce5b780eb5be.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2]

-- Cycle fingerprint 67ff0d171e49c0cb1c395887fd3ee03dd62ef3ca291c02b9066f21fbafc84764.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 680fd2a53eff91b42d82e772929d6e97160cb1fe99d9f06af1d096eb259bd330.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 6eea9c28796248681967b34bd2b4cad79dbf9c71db06e5e99389c683956db06c.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 20 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 6f3807696635edb8d683f38a5e8d7acf0c33d1956aaf85e99b63f5890eeb214c.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 20 0]

-- Cycle fingerprint 70438afa9f2a3053502e20e2b837de3982f279cc180bd0d1bbcd768b467d18a0.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Cycle fingerprint 7149a86816bd3a0f1c7aab2219f34fbc71cb1edbd187e39adba6c5f097e0302b.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint 725ce015cf2a44b111c860d32f961298319e4042e59f65321c9d354e7d7d1b2a.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 726ca5230484ea41b6ce9bf76d1de7238e57a00645956cee271d9df2824314c5.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 730060e99e944ab942c6a2582cb3b5b49c2478d76c5dddaf1b8fd743a8013d03.
def localCycle00073 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 2, .gapLower 1 2, .gapUpper 4 2]

-- Cycle fingerprint 73f3f6dcd818f2d513b755968b14e5f68331dc986cd7ecf0555019e7094a91ec.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 767d9b0ffdcfe8f58d160e0b6edebeab67beb813c945f957557c2187268b5145.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 7683fb602517f8b3a14c56abbb5c2a30651e93114f11b1fc987054a0d510da7e.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 1 2, .triangle 11 0, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 797952f2e9951441611524e69123a16b685e8e4b2bc30c034bf8cf92ccfde2f8.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 33 1, .gapUpper 5 1, .triangle 20 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 7a2947c5403ef7bd042ffd2da8c367f63f376eae3b9f24dc6a6459070f256913.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 7c755c47c567829957892012aa70aebe081830e70da30f98f4c6a96782c1392d.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .gapLower 4 0]

-- Cycle fingerprint 7c809b178a96e6558457d75a4e650a0bfedce7b0e5827433670f336db9d96a40.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 802012efaaa9f46130b9e5c3d4fa00d9a396d329396b77fe09bd710028ba08fd.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 21 1, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 80bac2f4529ee616fce93251665ce9cc98e0f6d26af6ec9e4c83bb30c5d7b29a.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 80bef679607fbbbd0e4c9aa747f1754ef0686b477aa34c489216fc03880cc142.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .triangle 21 2, .triangle 23 1, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 852514eb1257b255a3ad0254c3315234e05645632b33b10a6fed1c8a12fbe4bb.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 854fbde85cab74443ac0be48e01796f455bfd95e0c9ff8306e4b36597ebf10bf.
def localCycle00085 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8735c55ce1e438e4d2012e0ee2ed9c16d7a14d6887cdba1b4b56a4ba878febae.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 8e50c8cc281172b5610952c81ae810a1e23dbc46de424dc7a27c3bb53c8d809a.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8e9f7bf395b2d15a679971bfa562e3bced1f191286d6fb740ed3934e3015181d.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 90b89fceb3307ee79995dc67267cbde7c619995c681d2309e6e06fecc15013bd.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 925c73822b18f319350764c2ab4ec59e560c278a2cb4575c3e5ef3238c9a53e6.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 9456aee03d561ef51839c94aac2b3be840942a97cacf13fdceae40bb60fab667.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 96a167fd3efb56c394391539214931e580ac9500c999656447b06de1d5baa36e.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint 9ab94754552907fa89250eba0e2654cc633bf9b92bbbf81c7bb659b0cbe540d1.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 9b072b6173d2c32b1342d9cf8bc1530413e633deec7caf4222f8526bcb830b3a.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 21 1, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 9cd068df34397e9e596af31de2f415b98f0932c7f6edb8617b2ad4b9a158b946.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1]

-- Cycle fingerprint 9d74d6b1e6a2aed4b4ee2db38916093308d80583c6f6cdc0b42094717b0511a9.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint 9dea9290d3278350bafc47a2142fd59a1f2eba07893b972e56490a56e2eeda64.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 9eaebeaed31d6e1da39d264df9ba7c2d348bc9bc0f57d0fcf412a97f7338847c.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint 9f16c253f991cc435a52bb9490137249c0b69a50ae618af3f1eabbb29618cabd.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint a027c58da09fd58eaa839709dcd813972234828a7c0c78658909678399f0950b.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint a0cb4325842ed3f8dafd73464f2511e4fa2a9193291d80672178821f72967117.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint a181ecbd2479d60ac019f291a082f0dfc5ca2d68ece20017382e340135233d75.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1]

-- Cycle fingerprint a1a60cc9e92f2f4b5fb29f1b8259da1a8462bd04d16c95fb20a8be2cfd152418.
def localCycle00104 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint a571fbfd696a1a17ee64c5acdd451bb6f40dfee7c0cd93f8e74dc24ec911ddd8.
def localCycle00105 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint a77122489165686c8444a93240c7fa1b855ea8220b08c7f5e0551b25ff1b4762.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint aca7dd9ab33b4dfae5b40a8c755c2919ecb7f1a448c38f031c82d3613ea51555.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 1]

-- Cycle fingerprint af79417aa784b21ea002737a4af0a2e73a537b5c3c56c679b30cd3cfd085c98f.
def localCycle00108 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b0fc31a52e1bf1fee126f787184a7db6bd006b6531c63e05a572f15c93a530c6.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b36bba6060f76060e82b96e30867bf44447c7d3a4d58ee840200aaa1f44b06d0.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b3d41b171d64f688404ec3728ddc23f8ae2aaeee215eca1d0b73ad1be07eaafc.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint b548fd84fb23f473baacfeebbecc4f3c08f1232798e6f74004b2072e0d996c87.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint b6b59316150ef2f83c61502c3f4ea14f5644ed787644632f729a0506240339b6.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint b6d068bc8081f2c491a9ca2496f1e617e763d30adee7b90abd374dd02e4ebe6a.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint be287d86e67730f9976c3f5a56ddd2341b9e52e65e8be84b585baac244217a7d.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint c14e47ec39f887746842d5e7e76bdde5d55d7b6402e5b2ea7fe2b7e927493f46.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, -1, 0, 0, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint c27512d80ebd0e24954f2b92338b708ae4a5b86e732fddc6fc4a79121f134ce7.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint c2e64ebe3f6ad3abf9fe32748c069d0ba97b69fddbb4b4940445e638406335b9.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c423e5183aef636a4ade565eadaa3d2c06f10337398c5db5b71b25dbe817f926.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint c469861d18c69cd856a61c72040b0b05b4e23af01f42d3c3dbaa67150d15846d.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint c56bb8e3afb5687e9c319711aa315b26ba129df1a92c12ff3b17622a8d67bb08.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint c8a1bcbb9dc54b021aaea8238645cf18d6294a78c04c283a50718242e46e61a8.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint caad55c4ec909706c540f73e532d2ac5411f1c27e2b0ffc0649846d0226d6815.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ce6e1abf79aa021d92ba330e85f531211cd884fd739f128dbd396ed26da25d65.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 1, .triangle 21 0]

-- Cycle fingerprint cee51fd81ba6fcd183adb53809cbfa89056fe4cc9b1e51d735c187197c430207.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0]

-- Cycle fingerprint cf43dd60a8771830a4fc7c91c67e68a41fe34bfb9a6dee9e4976516c5fca04ce.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 2]

-- Cycle fingerprint d17805ecf56ee40f6d3831e01c2edf39ca2789d9a87f887dcea516136e4bd838.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint d3187b71694739464c953c54220a8d6d75b43e6d874d4ee876994a366ad9005b.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint d519f34346b4a012e06e53bb60eb719a6ce4e37237cbeb286e4856de1d2277a5.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 20 1, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d6de72a1d835151b50b854bdef41625f60ec9f2903ccc088c20cd3297d8d59c7.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d7fec1186bf46c141ab9c11d72e7c68190f8f8f092ee6a4d0d732098daf5e241.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint d868f909cbc92268f5a44f7dac4e626c29a8c5a83efef36d06f45abe53d38039.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint d9eb782611db1ed940523d1318afa239404aaf5a53af87768c3ad72be408b58a.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, 0, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 2]

-- Cycle fingerprint daa0fa5090f5219187584d8a2136f79f730a22562185803a93470eccc1b05e6c.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint dbde3065a8ff7a4f531371977eebeebdf89cc329d785488b0e27fbc609f31c63.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dc0cb0c4d1466ecc6f4e7473638b7b3c91969bd406e9bedc4549dd371b5d6d25.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1]

-- Cycle fingerprint deb71d55929dff3393590eb5ce7d8ad586fb473688affe7568fc360fd869050f.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint e14f7386a1e5116bc964e4b6ee45ebce46d6afd48676c2df4a1eefc5b251c2c9.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint e18df3d26f3949ba56d7dd8cea075c6ece30d9f9726970749a7c43b862137428.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 2, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e37e5cdd99dcee94e1ed35639aee87ee32830d60b128eead6aa24b8ce04ca703.
def localCycle00140 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint e38c3880ade3bb2548a127fa286dbc417d23bac643424998021eee3f2d15f094.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e67a5f009f7720d8807168818f6390c49848236374d8edfc14c893dc237e034b.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .triangle 16 1]

-- Cycle fingerprint e7966d42c663fc1b166cfee0de850eee323d433b728ddfa8251fec99ad0a334d.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 2]

-- Cycle fingerprint e7b2c0e309830707b7d3b6e9307a7584944165756be6ed73d5f1104c97a8ec2f.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e9add9c1810adf22f41685ec7b04f7a2b34ce5f96aeca5f30874b20d62538064.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint ea862d8ccd3b5f37ad8689d56301fffc68bac436493280b98d49c108bfbc494d.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint eb83a168578c0907b3abae2e1cfe58a55f30775070a2552e85d7be209227c5a0.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint ecb82e192ac79ebdc15a72889efcd2c670a1b3e55742230a5e71713520d212a6.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ecbf24a7ba79797a202e3cf6d4c7629edbc8648bfc636867a4ba50c8d517f245.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f05044817a27abdd41af5a4a9e27278c4c527ecc896f0c49a68efcc3b8bab8da.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f2e31e865b3429ff62b0174438f291a719850994c43de1bc20105970e0d97ce5.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f2f3c9daddcfb3b6c98cf16eda8ad8203fb76f0f629cf38858ea3bdb6fc7c73c.
def localCycle00153 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint f372a20b10b5f0ac3b09235c6ce13b95dbb2b4c9e8c0cab7381f81a7abfd9ab1.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f53a4571f219eeaf8761169e5eb2951f2974c9cdc2c03090d878493c5360aca8.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint f58bb0ddbd73196bfa8c146431299619aa46e9f96d0f485388415e5007f365c6.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0]

-- Cycle fingerprint f7f0be4cd4ca9725791e994c07ef6241023b0057aac353562d397ff821f929f0.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f8ddc4aa5ea13ebe3df97ca80fd75d4cc700e3da80c6ade6aeeed363e9559b8c.
def localCycle00158 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint f9997a8453137b4f1257f7f8ee3e8764770616fb3dd9388a7330427334e09186.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .zero, .theta 6, .distance 1 6]
    constant := ![-3, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint fc7977143fb0aa3d521f51b018e84cfd654f38a93758347c3475cb026874020c.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 3, .distance 0 4]
    constant := ![-1, -1, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.triangle 12 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 11 1, .triangle 9 2]

-- Cycle fingerprint fcc3bec42e1bb6f7f51467fcf1fc6d4b697edd15e56765b915f19db94da11147.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint fe24eff8924217eb00654a4a369b622bf994fd426e8967da17e67fb915934145.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 21 1, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint fe76f51574617394fb33866aeae03b36388db8830507c36edb263667a3290d81.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 21 1, .triangle 20 2]

def library : Library := fun id => if id < 82 then (if id < 41 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))))) else (if id < 61 then (if id < 51 then (if id < 46 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))) else (if id < 56 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))))) else (if id < 71 then (if id < 66 then (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))))) else (if id < 76 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))))))) else (if id < 123 then (if id < 102 then (if id < 92 then (if id < 87 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))))) else (if id < 97 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))) else (if id < 112 then (if id < 107 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 117 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))))))) else (if id < 143 then (if id < 133 then (if id < 128 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))) else (if id < 138 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))))) else (if id < 153 then (if id < 148 then (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))))) else (if id < 158 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 56 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18432)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 113 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18433)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 59 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18434)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 36 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18435)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 4, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .low (![107, 97, 58, 117, 85, 25, 33, 93, 61, 5, 104, 83, 20, 31, 77, 104, 120, 13, 77, 104, 38, 89, 104, 14, 67, 104, 104, 124]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18436)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 27 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18437)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 27 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18438)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 129 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18439)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 110 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18440)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 108 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18441)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 62 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18442)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 1 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18443)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 92 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18444)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 161 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18445)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .tail 19 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18446)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .tail 19 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18447)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 132 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18448)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 6, 2, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 4 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18449)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 19 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18450)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 19 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18451)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 9 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18452)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 11 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18453)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 11 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18454)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 11 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18455)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 11 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18456)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 11 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18457)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 11 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18458)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 4, 6, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 46 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18459)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 141 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18460)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 6, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 34 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18461)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 0, 5, 2], ![3, 6, 1, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 72 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18462)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 4, 1, 0, 5, 2], ![6, 3, 1, 0, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 119 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18463)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18464)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18465)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 71 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18466)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![1, 0, 3, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 138 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18467)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 6, 5, 2], ![1, 0, 3, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 157 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18468)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 4, 3, 5, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 3, 4, 2]], proof := .tail 64 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18469)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 3, 4, 2]], proof := .tail 64 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18470)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 4, 3, 6, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 3, 4, 2]], proof := .tail 43 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18471)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 3, 0, 4, 2]], proof := .tail 21 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18472)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 3, 0, 4, 2]], proof := .tail 21 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18473)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 4, 6, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 3, 1, 0, 4, 2]], proof := .tail 106 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18474)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 21 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18475)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 0, 5, 2], ![3, 1, 6, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 21 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18476)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 0, 5, 2], ![3, 1, 6, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 145 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18477)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 0, 5, 2], ![3, 6, 1, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 145 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18478)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 6, 4, 3, 5, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 1, 0, 5, 2], ![6, 3, 1, 0, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 65 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18479)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 109 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18480)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 91 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18481)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 57 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18482)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 57 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18483)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 2, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 154 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18484)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 79 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18485)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 2, 5, 6], ![1, 3, 0, 2, 4, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 76 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18486)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 4], ![1, 3, 0, 2, 5, 4]], proof := .tail 47 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18487)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 2, 4]], proof := .tail 161 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18488)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 2, 6, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 2, 4]], proof := .tail 63 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18489)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 2, 6, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 2, 4]], proof := .tail 112 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18490)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 2, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 42 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18491)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 4], ![1, 3, 0, 5, 4, 2]], proof := .tail 4 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18492)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 6, 2, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 0, 4, 2]], proof := .tail 4 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18493)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 6, 2, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 0, 4, 2]], proof := .tail 112 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18494)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 6, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 114 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18495)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 4], ![1, 3, 5, 4, 0, 2]], proof := .tail 94 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18496)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 0, 2, 5], ![1, 6, 3, 0, 2, 4], ![1, 5, 3, 4, 0, 2]], proof := .tail 112 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18497)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 114 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18498)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 4, 6, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 0, 2, 6, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 100 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18499)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 0, 6, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 100 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18500)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 6, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 100 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18501)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 1, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 54 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18502)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 1, 0, 2, 5], ![6, 1, 3, 0, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 69 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18503)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 152 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18504)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 57 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18505)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 5, 6, 2], ![1, 3, 0, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 150 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18506)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 5, 6, 2], ![1, 3, 0, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 151 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18507)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 0, 6, 5, 2], ![1, 3, 0, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 48 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18508)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 5, 2, 6], ![1, 3, 0, 4, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 152 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18509)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 5, 6, 2], ![1, 3, 0, 4, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 6 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18510)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 5, 6, 2], ![1, 3, 0, 4, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 138 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18511)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 4, 5, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 6, 5, 2], ![1, 3, 0, 6, 4, 2], ![1, 3, 0, 5, 4, 2]], proof := .tail 7 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18512)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 0, 6, 5, 2], ![1, 3, 6, 0, 4, 2], ![1, 3, 5, 0, 4, 2]], proof := .tail 84 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18513)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 6, 5, 2], ![1, 6, 3, 0, 4, 2], ![1, 5, 3, 0, 4, 2]], proof := .tail 64 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18514)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 0, 6, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 1, 3, 0, 4, 2]], proof := .tail 134 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18515)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 6, 0, 5, 2], ![1, 3, 6, 0, 4, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 0 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18516)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 0, 5, 2], ![1, 6, 3, 0, 4, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 116 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18517)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 8 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18518)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 6, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 0, 6, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 3, 1, 0, 4, 2]], proof := .tail 82 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18519)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 6, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 145 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18520)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 1, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 16 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18521)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 6, 4, 5, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 1, 0, 5, 2], ![6, 1, 3, 0, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 111 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18522)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 101 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18523)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 127 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18524)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 30 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18525)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 0, 6, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 148 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18526)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 0, 2, 6], ![1, 3, 0, 2, 4, 5]], proof := .tail 101 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18527)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 0, 2, 6], ![1, 3, 0, 4, 2, 5]], proof := .tail 32 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18528)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 5, 4, 6, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 0, 6, 2], ![1, 3, 4, 0, 6, 2], ![1, 3, 0, 4, 5, 2]], proof := .tail 148 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18529)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 0, 2, 6], ![1, 3, 4, 0, 2, 5]], proof := .tail 146 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18530)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 5, 6, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 0, 6, 2], ![1, 3, 4, 0, 5, 2]], proof := .tail 138 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18531)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 5, 6, 0, 2], ![1, 3, 4, 6, 0, 2], ![1, 3, 4, 5, 0, 2]], proof := .tail 29 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18532)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 5, 6, 0, 2], ![3, 1, 6, 5, 0, 2], ![1, 3, 6, 4, 0, 2], ![1, 3, 5, 4, 0, 2]], proof := .tail 98 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18533)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 3, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 5, 0, 2], ![1, 6, 3, 4, 0, 2], ![1, 5, 3, 4, 0, 2]], proof := .tail 45 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18534)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 3, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 1, 6, 5, 0, 2], ![3, 1, 6, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 1, 3, 4, 0, 2]], proof := .tail 90 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18535)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 4, 6, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 5, 0, 2], ![3, 1, 6, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 3, 1, 4, 0, 2]], proof := .tail 139 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18536)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![4, 6, 1, 5, 0, 2], ![3, 6, 1, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 122 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18537)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 5, 4, 3, 1], ![2, 6, 4, 3, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 4, 1, 5, 0, 2], ![6, 3, 1, 5, 0, 2], ![6, 1, 3, 4, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 115 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18538)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![66, 41, 2, 80, 159, 12, 68, 162, 123, 15, 142, 130, 75, 96, 3, 35, 153, 95, 103, 23, 147, 39, 140, 105, 81, 26, 52, 44]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18539)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .low (![37, 41, 163, 80, 159, 12, 68, 162, 123, 15, 142, 24, 75, 149, 3, 35, 153, 95, 103, 23, 147, 17, 140, 105, 81, 26, 52, 44]) }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18540)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 0, 5, 2, 6], ![3, 1, 0, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![125, 41, 2, 80, 159, 12, 68, 162, 123, 15, 142, 74, 75, 96, 3, 35, 118, 95, 103, 23, 147, 39, 140, 105, 81, 26, 52, 44]) }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18541)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![99, 156, 73, 80, 159, 12, 133, 70, 137, 15, 144, 10, 143, 49, 3, 136, 78, 160, 103, 23, 147, 126, 140, 105, 81, 26, 50, 44]) }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18542)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18543)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18544)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 55 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18545)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 5, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .tail 55 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18546)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 5, 2, 6], ![3, 1, 0, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 158 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18547)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 60 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18548)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![4, 5, 1, 0, 6, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 131 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18549)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 4, 6, 3], ![5, 4, 1, 0, 6, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 88 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18550)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 4, 6, 5, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 2, 6, 5], ![3, 1, 0, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .tail 155 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18551)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 87 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18552)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 40 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18553)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 51 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18554)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 5, 4, 3, 6, 0], ![1, 0, 5, 6, 4, 3], ![5, 4, 1, 0, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 135 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18555)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 4, 5, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 128 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18556)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 5, 6, 2], ![3, 1, 0, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 86 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18557)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 4, 5, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 121 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18558)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 5, 4, 3, 6, 1], ![2, 4, 5, 3, 6, 0], ![1, 0, 6, 5, 4, 3], ![4, 5, 1, 0, 6, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 0, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 102 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18559)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18432 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18432 ≤ id.val) (hhigh : id.val < 18560) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18432)) = true := by
  let j : Fin 128 := ⟨id.val - 18432, by omega⟩
  have hsum : 18432 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18432 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard144
