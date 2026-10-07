import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard004
open N4R2OuterLeftReplay

-- Cycle fingerprint 01245ff6ec2d424a041c2c1f51beea4d05d0f87befa193b05a9427e80e187bc3.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 018e1db27636a214ce20e3a9a2e303dbec94b51a8edeeb06133eecc14c9ee307.
def localCycle00001 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1]

-- Cycle fingerprint 029d60c7602805fca6913022706a0ace5f265d204a5c18cf258d36ff7f3acfaa.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 034203772c447a0753e7ec3a25be553dc1fb26ab60632806d729095e196ea304.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 04566cd1c4b2bddfe77e5b2cc8fcbf666eb5a20bd9c5ef4da24f0f29a8dcf247.
def localCycle00004 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 29 1, .gapUpper 4 3]

-- Cycle fingerprint 0696dfaa52fe5094df7f8188735f19d6f430531e0427e5f263fef8716f5d15ef.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 0749a94856a0a182cfc3297ecafbccddddeeb3506245ed6a570fc2682b1ef507.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 4 1, .gapLower 4 0]

-- Cycle fingerprint 07b13ce310877dd96c2ded4ab924d4fcb312c2d368ab33d7eb2110be6d9210ae.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 0c8f30992474a9ef38cef7ce9608d63a00e8e31ec820efe7fff7d1957f598ca9.
def localCycle00008 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0d8e222b7bc616ded1bcecde67b0c86cb902a2ec865c72af3ecbd286ee0ee5d5.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 0ec1416dd810a8d4148460c483469f9a15cbd1588d1abcaf191db0156a4b24f0.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 0fa673db412bd8c1232b97465001ffc745932f478f329b1118dd32e4a102a521.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 11677d885c8fbe19592ed111f7d2a70e4dc6e7b7298ce2134c414b6290273bad.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 4, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 118a38a46f3532f899870d16ec2889ed20a4dc301926e76e902be5e7a5d02b45.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 132d25a7b085e51256dd11cbebec49088b948a11c7ef59aa945ee9e15b7c4fed.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1862a4af941cdc0606457a2c42bd38e156145e31c85d980d248c21e0983ec271.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 18cbb1368928a32e4819fa20a4006b5a74874e51611ab4b37cef50a1590a92bf.
def localCycle00016 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 18ecc1c29c437cde7beea7ef58725a8ec9516dafd70264adcb96c228d2801d99.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![0, -1, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false, false] }
  origin := ![.triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 19475d48b9d2610ba2736d2732cbf26f62673d03c8b4fb8f5ffa32f0bcc7a4a4.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 19c8df0bc516efae486419ef2f6d8e1b4aeb2666fbe4541dd70151415e2b49e1.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 1cbbc2a81a8001cd7a180fa5ba59b357e04e914db305afa61c0d1ecdba2d1364.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 1edcc6716266b043e29f421551cd687da65f282d9c36ce5b109e0ea72a0be602.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 20084118f9d4784216edff5c6312486a066eb53502366caa3f63d118f64eb91f.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 18 1, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 21577032678b3b7507bf0725bb5e1f54e3a82509886f012c3fa32a5e9446f9a6.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 21f48200254606fb111912e5e028b0eef083fdbaab7a4402bed29e4422042863.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 17 1, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 230f59f59f2bf39032e43048a1ed5937f9a44d58c03d631a64fecb7682292c9d.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .gapLower 1 2]

-- Cycle fingerprint 23811e443e39933b91c62c66295a60473d4455153e913acd9172f576011af1e6.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 2679a1a8bee69d2610ff75551492b329e2141c8afd3d1849711868ac1646c1f3.
def localCycle00027 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 26f083c044276236091a2e3a4c5b9c04d4fff3b8082689ec3dd77f68874e830b.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 28ff76ba82b0c8502c22490a799923d3329a220728dd089e835f9f7ef133c9b8.
def localCycle00029 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2de7733255fa8413b0509e891f92d89596ee0462b51f923581730bf745517dbb.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 2e3c75cfc75b0aa35a54f21f91e98a10ee2c7beb889ad2539d512fc3ced3bd20.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 303f529585f03c81ac187ee4d3034265a3e55c180d364fbfc0a05dac9aa08425.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 34d8c2c0c4b88f639b361c3b00a6b5e74cdcf04d45ece6a27a677c738e93efc4.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00036 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 3686c051613df8f7819c3342c74bae231bbd9d30b8c9746f70c82f9b953c4e58.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 385b00116db3d572c098ed1b5ba2fcc645463f1b585e81a309f1bf2eefe84961.
def localCycle00038 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3c56874611400ca5cbc775f36e669b5927d5918548c7f130376d7f9c0d9e9d3c.
def localCycle00039 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -2, 0, -1, 0, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint 3c69647f8138deb8d0e712908df4f6631db751a49ee01e7659eb8ed9c55fb0eb.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 41de3557ab8a97e595823cf8822e6912222b2d4c676e55324945f55de6b6688f.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 431f0f152a995af9b5761718a21f9d740fa06b1e0a66f709c1997cdc59e0834f.
def localCycle00042 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00043 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 450504e35f1d4a475b5d68f21e450b6fd3863a8df31e49b01e65ca45d1bdaf62.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 45524cc97ef5056362ca8f11cf3fe0c58f012a5cd396f410e12a6a52cce09a80.
def localCycle00045 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 46141d1289555f9827b3f475616466dbf1325b773cb680e056d94d809013fe2a.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 479a2a4240b54ba514f6e1f1832ba681a94e3b068cd9449c7f6ad2f536271a29.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 48e937d9b23628303be1d14de8aabbb3133b1b1acdce9f3b1b881f744b506103.
def localCycle00048 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 490668bfd64c9631385e08fa12799b1eead7e6c8e98945c5599e322a0e491996.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4980114a8f81f864eafa7a8a8152a81025171242ea6d34f2b1f94e7cd2a772e3.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 4c6058c82ea836ff278833e6e9276ab2e22ed749ae23244c32ee23b2bea26f51.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4d3e9acd5de85998033d99265a1d12222ddf925bfba493654c2b8cfc885148ab.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 4d428e7d3773bc6ac32fdd108879adc25900d99cb432b954a9db2b3f317802b6.
def localCycle00053 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 29 1, .gapUpper 4 3]

-- Cycle fingerprint 4ee5fe55505fc19d710767a7e3c74c5fcaefefa4764ad88752ea88766b3e3cf9.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50f85188dc1d1ff8764651ffc850fa4c19633aa06d66df18acd462646928f48b.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 53c0a47c0940edb7eb9673f3cf4e2ce5123287629b526e3097836fff61c22f41.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 55564a8d5c22b89b1ca374205393815291d332542eb4cd58ffed6f3307cb8726.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint 5667dcbedd7fb4acde5016f49a796aa3693d8396f3cb08810c6104b7c550f541.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 5a82ce6d952b24a5defaf42f0fa6043cba08aa5b0858b14c530b6ba9534fe259.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 5bc94368459a44f0030d5c602d06f8f52142d51c9f1cc44122763406a5e0deb2.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 5d8db66bc7fbf9013ab6dcde65179decb223c9baffb857d2ebc339e6fa9f289e.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5f22717d63be107dae5bbda4d2a4193393aec448c9d8ca8eadfb922e1139e735.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 17 2, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 60c6555bf9a732e48290a5735a5f432b251f312c4a78818715c9d8ace881b6e4.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 612603d3c825c20043e45908eb83b58de25ce527ac7ace6d45b26e8b02cc1235.
def localCycle00065 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 630cf8786dfa976e20f346965b469237c26a09b83a1a1ab0b7ff663f487d1a75.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 66da2de397098e18325d765806f576844a775aa90d49b3fe35800c07a799fff2.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6939262d524f126b1032082bffe3fa078f2099d3a0c73fbf88987bb1d6416761.
def localCycle00068 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00069 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6afec5dd0a16cbc6df5f526382291a4ec7c5516a7100c4a237dc4c631f3bfa7e.
def localCycle00070 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6c180d07378f87605504491981ec0e10cc5d16473c28befbcfae9804f92a868b.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 6d8c2ca3b001b27079eac63e5d808bd4a2a1c508744e54a9c0aa31402d12598c.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 6ec2ce38305f05942b5c502802bc822a4776737067ab05b37337882b5a411d3b.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3]

-- Cycle fingerprint 700e0842b6934611b315465ebf5f20b1d0afd12b72097fe27b0431d3bf89c8b2.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 70af474136c64a2251232a516d4a77d46043787e503cda8cfd4355e7d969eec3.
def localCycle00075 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -2, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 73beb4dea99ccfaf380707b9fbf7af9d148de2772c09e5a2cdbb6875261f2927.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 73ce53860a792d5a9a2b470928d6941a7506a190eee3c6d9e230062dd916fc78.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 73e490c7b7ef9a912103b14adcc25307261646c3065e07a23a919260e38f5e66.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, 0, -2, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 17 2, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7495bfdb3fee9978c8e431b34db2d536f883dee51b0003a59e6d49ffff7f2303.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 75bb79d5ec6a14ec6cae5b6ba397d39df59586c0a04827fc8aa8e2e1baa3ec48.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 75c0e8b1c6c25c2b879fc73fdc40f06631e138700ab1df1185c35d98f3b8f8dd.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 783e2b4add81bcb2d13abf40f690ac662e5fef18a2cd1c57941f7f666c7df84b.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 79d22e7a4b4f72575d8924ed9f4b04a323cd63649a754e8b9219cae7ff7077aa.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -1, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 7ac11edabceb51a6882dceb6d36755c7fc16f99cde664db324ec6a484759bc18.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 7b4ca5bfd400ec5d2cb4bb47ef69bda91471a6a28723e51227c8124846e654ba.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7dd8236cd31226ebbad644d511d485e3c84979e589594cf11ebd49f47665cdcf.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 80f1575736defd5f24561a67d2b0e3db82ae40e04df84e4a8a2e0fa46aa7aeb2.
def localCycle00089 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 81f6484e457624bcbf65a231dfbb68ba91df1b26f5614ae93bd4eb782f2c02a1.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 828031c63fb1a9a19e8571ebdfb52f2c4f76e19345f5f3abd657451d4fff2c97.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 83c40cea4fd543ef580bc359a226ababf9116075ad483c78d019e061b07c9d9f.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 83d25514645b1a16d4ee85d37c43293f2b546fa833a886a9849077e3195a9980.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 87f84aa310e6a83c946e63f6ebdb2334f44303567cd611b27d0f31bd70e5aa62.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 88824eb050533e276747f73f89f961a7c63a52789bf6f26f5fcaa3b71546cde6.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 896da1bb7299d9c7817828f0879a6401048ea57e7d2bd74eb522aeb5eb6a2244.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 8a94709f5f8dab496bbdedcf4a942ca601d3b6f8b7b269fc8b7aab559948567f.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 16 0]

-- Cycle fingerprint 8caa566e6e62adaf3c1f9bb6124029d99d9e73cc8e91c5943ff2545ac0827c9d.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8dbb98e1d739bf633202951057ce92e3e365d034df19b08062f1999735a239eb.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 8f5c74645dd48d27d79cd3360f7593409287b42dc071559353aa2cad851f4c6b.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 9114dcf2ba44e3c43bbd85c4046dbc94b32969c6477fa8426ddd2dcfd584af4a.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 9259f240b23fdfdd58a7d5329ddda141c049945bcb023766cb18de8758220188.
def localCycle00103 : Cycle where
  length := 14
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 2, .triangle 20 1, .triangle 19 0, .triangle 25 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9299395381ad03266d21436831ce123948d82eba42fc8bc40cf4eecbd340d23b.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 962615ae91182d88b7d3d04ab9156c1edc55e13a220750920767238474b57c1b.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00106 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 968fec239115fb554919b5e189fb5de6a19f0c9faf02b7e8021c2b69408661e3.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 98d155f83402e40fc701bcccb2070315b2b5c7c18b7151e703774304fac8205c.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 99fbfa4a94ea5de2bd35f6d7235976f319569fb117fe9667458e5eb1e1b69e31.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, -1, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 6 3, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 9a5934a5ddad474ee54568a6e30100a56bf779c86a0f7b487a82aeb82011fd04.
def localCycle00111 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 9c2f527a6c07a067310b6488c0d594eb62d5500b77a8cae446d8d2f8e65192d5.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 9ce3b3a0ee41a5e716087698854f5fa40d709a509b310516c75d9bea6c8fd602.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint 9ec9edefce5d0e5776fb67a58a44bbd3659805088d26cfeee62fcae21c52c178.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a0c1496baa8582c59383e4c0df87d2a6485f28899fcdbab86f216d475e9d631b.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint a179fcb82e3433ac48064bfe3e554b8eefce5484667951b2620289758fc13bd4.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a1a9ce70e1f3a6b8fb46e9b4c08ff6d06a399ffbcbf576588e00185d948908dc.
def localCycle00118 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a1e82bdf8b2be7b8f35a93ced9e33a2efa967965c34fdbafab56953c0a6eba6d.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a276e83bab35030954acfca8e5d30e52b00d106ec370caff739efc9077e952ab.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 2, .triangle 20 1]

-- Cycle fingerprint a4798bb1d585c9e4e49b7b066b89750b3ea400eae2e0019b75a757b11f7b2761.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 4 1, .gapLower 4 0]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a5b72063a6f3312b7f93a43d3779122b27cb4b0b1831998e6775b08a66b4c4f7.
def localCycle00123 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a5e6e29c4770fe6a3166e771fac3097d77ea25237cf357f92829a056a6a3bfc7.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a765a24027c3d73c7b38a5d3423a86ad2cf5bfc7e7812ef36c54c403898da23e.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a77718cb5c484f5903d8a1981aae50656a247eea736626e85b7c977cd2db0fd4.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a7d8a4eeeaf1c2220c6dd3817115fb986df0876d4e5dc2a50450c8f1ca13e72e.
def localCycle00127 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint a845def362c73029eac705a408445e24060c1b43368c1a2e245a80b1777247d1.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint a9a1c5ef5da821188b017cf6379f82c1e15c339d2efa456de006f53832a95a8f.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint a9df1ee4d931fd1b3ca4e6e1b167f36b61ee24de8d9de845c23f0b5304f297f5.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, 0, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .gapLower 3 1, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ab6e4c2274aac93b56f152633829cbb9f2968dbaca316e6065c8fea117388a90.
def localCycle00131 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint abf40c231646ed63e816a039da6d845c9c0df09069f15bc80fbb1c706fd7de96.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac9dbced26c9859ac2a121c08a03873a0ee43666c23dbe47cab5727a0863590e.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ae4af1835d651df2a88d86558e93d9ecfbece4f2de15da155454f16b76deee0f.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint af53df9d225e34764582d21f9e3a2b5d9f03dc19ddba02bf2c1dca563ceef19f.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint afea453f63019f72fec5eff28367ff3f48dbbb2957b331a88dcc09483ee25da6.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 26 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 17 0]

-- Cycle fingerprint b0b12b393ac63663242bbcb75a4feab9fad278c8e3d63b97e7c57876ccc4aadb.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint b0c92ec97c3c9a3fdc3a3ccd1f74e10c67b7ca8aeee6a6568d557f8d09a72334.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b2258e091407d8f87f336eb34bf2078d8f38bca77dd80f5d5e91e7f68999b22a.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint b2264499db48a1e95e9b29f3e0619fc7ae613efce7906ecf93d00a3c6d94343a.
def localCycle00141 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b2adc7710e25403ba685114b7712c0e8aecb1d67c80a1411cb18de83b2d8f7f8.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b2b6266edb92e2a2af1b577c008da24c28807ae113fe5db1dc75d93b186e958f.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b3df96631b534efe55d78895803c0f0a009bf2d8615d7ff6c088b3b8073ba59c.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint b4dd15aedbb56dd576323977ab6c28ab33707136b5857ae9c1617b2754863f1a.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint b6603c48ac9eac8a755620596a04c29fb1b853b4a3d145082f43d3064414f811.
def localCycle00146 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint b68e6ace914c59145601a42e9ca9722c6554cfc58b32926169a28bcea4d585ba.
def localCycle00147 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 30 1, .gapUpper 5 2]

-- Cycle fingerprint b855e33a09ce86d7ff501a6ce37ccd4fa61b449f8a03968850065274bb8ae76b.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint b8ab496e2beddf06491f279beab35659ef6ab3c9a4aded092c371a39d3d58483.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b8d6cf4f8d9a6e929c7ee197afa19a2f4323d56a83ee188fcd6c8418a0cd98b5.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 3, .triangle 17 1, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint b9bf819690e07bdc34ec28a0a169bd5c806962fe942d9b48b02b1887a7fdae57.
def localCycle00151 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint bd4eccf4435dc0468d5e04b5a618ed5bc55ff8ecd9bd4b8a1d27107106e3d981.
def localCycle00152 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint bf3ce67ab7df63f40e52956ffc01d132df0905011b4852d7f7427691b3f7a04b.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c05c14240d14493987bbfe24e556835b17687a462abce3dd9d6dedad9dafd4fb.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint c23d3e0c716af26f994aac75eab3f9bc3422b7d12eaba993dbe83d1023828cca.
def localCycle00155 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint c2cb2403d95d7312570f9c7a909cec66abba02da28a1b04dd9a3c0eaac014c7e.
def localCycle00156 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 23 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c4edb52769a32006299f180b90f4abd6f72662c3573d0e756c67e2d4305637af.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint c50e49b3cc249a779daa61e5de1452cc59375bd7d0a37525b6348a199df43b89.
def localCycle00159 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c5522ef87c0d276d2f427cd32441588804c5481cd2f83cfcff60a67298e16f31.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 30 1, .gapUpper 5 2]

-- Cycle fingerprint c5663c8ef956c386e578a2ed37f2242023653dc4e0a55f5c42eb708ee4195365.
def localCycle00161 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint c59b2ae221131ca1c0fa787476e152d6e1b6b6c46409865dae1374feab273c13.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint c5ad49a9bcd68b4da584ec3ca5a9a3c59ae80dff3e294bcd09346cbab098c5a3.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1]

-- Cycle fingerprint c646ce5fd3426db9ea3b3df395591d9399da259969b18cdf26d0e8c620d6fad1.
def localCycle00164 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c66c95489fbdc596839ff4d3f5c4df784ba2547b8260cbf8f0f25f8d9a4d4a4e.
def localCycle00165 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 5 0]

-- Cycle fingerprint c87299e92e7d274730626fdc2d62a2c64d0db1c67585a0352a1815798408170e.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c8da447125de360d10cb956b7ff25c111a91e25b9813df29409736f7d4b098f2.
def localCycle00167 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cbee9b30a0cbbef18f82f61203a5fbffe2f1636b18fc2ca9249b5bf1f5f9f2d2.
def localCycle00168 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cdc558b4a13fdd35178ff50b92da4d0bd92c218bbf040f6fb4bfed972b54ed1c.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint cf1c52029177f9cf995d99b57850d4e11dab02c4e111bc1696a5b6adbf576b20.
def localCycle00170 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d19187cdc50313c48ece799a32a0c2f10609ef26530c41e8ddd0d4be7b2cb75f.
def localCycle00171 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d3a2f333f98193ed6ac946031bb3308ec2f23182fc64884514c2356a672beb6d.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 2, .gapLower 4 0]

-- Cycle fingerprint d4b5491363c62fcfb4623cfc688d6ac55de21bd8e89f097102c3f84bd5069086.
def localCycle00173 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d57d88a4e9e62e3061282f7d60d8cc172bd708aa49af253f623359782f528272.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 17 0, .triangle 16 0, .triangle 6 2, .gapLower 4 0]

-- Cycle fingerprint d68d6d78304f955a62894676ba253a8d8c5b1419395e5b038825040658c593ec.
def localCycle00175 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint d77ce020a8e6ad29d17ddc377ea6a1263425f1fdfb34f43fa27949a1f1bd9d5a.
def localCycle00176 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00177 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d7a8b372e66efd2fe7223bbb7f43087a8de85e5f0d10859be2a61b24a72bfc99.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint d8d6d3670ec9de826e1e2c9e0c2ab0d647fc7f04911ab4bb63c254de8014cbbb.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint d967b4869fecf9f6845802ad4100552f22e5638beab30f14a95435dbf29eb6fa.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00181 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint dae872b7c9c59ccfb6643c99591471de2bccdf652b068d4191ee9242b49c49f9.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dc55fb13b13cb2c8a602500aeaa770f458849881b0a95fcf863c605d9f42207f.
def localCycle00183 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint de002661770d6322c012a339a6e0ed79b15fe7ed85367c058248173d7959085b.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint deb9d1ce1e2c8987fabc56948571d601297651d675ee9e03243563c8106bc8d5.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint df8e0b16f5ceea806f8a8167bb403ce39d85c8a95b81a6477c2f537b817e2538.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e181c17a4305957bd63f0aba9fada457e60d1788fbb31f7d4c69e415802b6c87.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 1, .triangle 17 0, .triangle 28 1]

-- Cycle fingerprint e31cd20ac8a54d1eefce3219478e06ab846a5ba96bb6fcda5299633ee15eca88.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint e36f2a587b5364e3372b12f3671b3b212815d5b290090fa9c512f989d8a3961a.
def localCycle00190 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint e3f19ce2a68d104258d773b72a580b1b6cad860d81088ddc026b54b28dc1d907.
def localCycle00191 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00192 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e5e95cf4bb708fdc1898b9018206ad0459a5466a1454d6902bc1d722596d614f.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0]

-- Cycle fingerprint e678b95afded36f5e849ab16311035e8ca5ce14acd056dc3b4086b66b6dfbed8.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e8189301220f8cc317f1ffb50e0d4630ff1243a2f9452f2f61d4e7f9327c1e2e.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint e981d5c252197d9a2574b72029690c57b29217a604904740e18d85f7ff7a4cea.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint ea215407c1010c8ce1bbfc48f35c8c40004eefaade2bc3cc578ba7b3b70bac0a.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ea5ae82a072824621831f72b84bf216b945fd5341685f7b299fb1a3883351547.
def localCycle00198 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint eddf63e31241f5d7f05b1e819f57af04af5601f58fd62b2490c17f9d6977f4ab.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint f254724245ec743c9632f872bc524e090e32f2b0e903900d97027299c023feb3.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f3a958f471d509b485616aee42d21671ce8b36515e3abf8423566b1a454e0d01.
def localCycle00202 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1]

-- Cycle fingerprint f57b8786c03050636f005861a322700f372e90384f43170cadd41edcef4e9cf2.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f5b7259ece8086d3b68286e14f4d06c4dcd8d595631434cfe5e74609b68045f3.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 4, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 4]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 2]

-- Cycle fingerprint f6a53982625753bc7289c1929fbfeb2e863ea2802a7ecc7afe720640891648e7.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint f74fc213e6543d702791d41e7f7d96a9c549d83d9d1bd263db037c5ae05883f2.
def localCycle00206 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f75918587eabedb1b0f5c373001b16fd0a71415dea341506f696fe965d9a90d7.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f957a9fc9e5b9b57af3277913bc85499b94951f82241a56bc773b1b6e7686aae.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 17 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fb14204a08602acb5d76b9b6b87ba8f0421b3853829d2001d37b66d56673b338.
def localCycle00209 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fd48e1d11c3726f8423fe1b507b371e49cd66ce7a05cd31df9d1cafb22ddb62e.
def localCycle00211 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 2, .triangle 17 1]

-- Cycle fingerprint fd75e9beb65379f9c95ad9e885161e9648e67314d7cef679cd62505cd1a1e1a4.
def localCycle00212 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint fff7f51045b2543260e21f3ac20655980ded4e408cb4e65de111c6fac5449813.
def localCycle00213 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

def library : Library := fun id => if id < 107 then (if id < 53 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 46 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)))) else (if id < 49 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))) else (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))))))) else (if id < 80 then (if id < 66 then (if id < 59 then (if id < 56 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)))) else (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))))) else (if id < 73 then (if id < 69 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))))) else (if id < 93 then (if id < 86 then (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))) else (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))))) else (if id < 100 then (if id < 96 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))))))) else (if id < 160 then (if id < 133 then (if id < 120 then (if id < 113 then (if id < 110 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 126 then (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))))) else (if id < 146 then (if id < 139 then (if id < 136 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)))) else (if id < 142 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 153 then (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))))))) else (if id < 187 then (if id < 173 then (if id < 166 then (if id < 163 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 169 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))) else (if id < 180 then (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))))) else (if id < 200 then (if id < 193 then (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)))) else (if id < 196 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))) else (if id < 207 then (if id < 203 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)))) else (if id < 210 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .low (![149, 199, 106, 146, 108, 127, 188, 133, 179, 117, 57, 91, 43, 30, 186, 62, 143, 181, 205, 78, 92, 25, 135, 139, 195, 113, 156, 137]) }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 512)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 31 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 513)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 184 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 514)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 97 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 515)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .low (![130, 199, 106, 150, 63, 53, 163, 133, 138, 100, 99, 4, 43, 66, 71, 126, 4, 181, 112, 116, 4, 32, 142, 4, 24, 4, 17, 4]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 516)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .low (![130, 122, 36, 177, 63, 53, 163, 192, 187, 100, 99, 4, 43, 157, 71, 126, 4, 34, 112, 116, 4, 69, 142, 4, 24, 4, 17, 4]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 517)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 28 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 518)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 153 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 519)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 52 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 520)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 13 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 521)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 153 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 522)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 50 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 523)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 88 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 524)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 107 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 525)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 5, 1, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 526)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 5, 1, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 154 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 527)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 213 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 528)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 165 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 529)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 136 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 530)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 55 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 531)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 212 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 532)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 33 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 533)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 210 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 534)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 140 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 535)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 0 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 536)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 80 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 537)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![0, 5, 2, 1, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 190 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 538)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![0, 5, 2, 1, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 207 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 539)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 59 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 540)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 178 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 541)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 168 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 542)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 94 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 543)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 197 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 544)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 118 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 545)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 81 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 546)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 153 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 547)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 7 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 548)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 26 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 549)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 550)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 144 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 551)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 200 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 552)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 191 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 553)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![2, 47, 86, 152, 108, 83, 208, 3, 189, 58, 87, 151, 42, 180, 169, 119, 102, 104, 194, 39, 129, 162, 159, 40, 73, 75, 111, 98]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 554)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 155 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 555)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 79 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 556)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 132 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 557)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .low (![114, 47, 86, 93, 63, 147, 202, 3, 10, 11, 82, 160, 42, 96, 37, 95, 160, 104, 201, 128, 160, 77, 158, 160, 14, 160, 22, 160]) }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 558)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 193 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 559)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 38 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 560)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 176 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 561)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 56 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 562)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 56 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 563)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 131 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 564)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 5, 4, 6], ![0, 2, 1, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 109 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 565)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 54 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 566)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 174 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 567)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 172 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 568)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 5, 6], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 204 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 569)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 35 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 570)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 203 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 571)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 51 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 572)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 23 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 573)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 41 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 574)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 23 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 575)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 46 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 576)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 105 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 577)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 198 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 578)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 3, 4, 1, 5, 6], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 161 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 579)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 3, 4, 1, 6, 5], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 18 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 580)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 60 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 581)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 164 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 582)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 209 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 583)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 90 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 584)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 4, 1, 5], ![0, 2, 6, 3, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 74 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 585)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 185 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 586)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 120 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 587)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 588)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 9 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 589)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 5, 6], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 101 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 590)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 5, 6], ![0, 4, 3, 1, 6, 5], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 5 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 591)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 2, 6, 5], ![0, 4, 3, 1, 6, 5], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 166 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 592)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 27 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 593)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 167 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 594)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 125 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 595)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 134 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 596)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 72 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 597)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 8 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 598)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![0, 6, 4, 2, 1, 5], ![0, 6, 3, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 211 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 599)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 600)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 12 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 601)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 5, 4, 6], ![0, 2, 1, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 85 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 602)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 5, 4, 6], ![0, 2, 5, 1, 3, 6], ![0, 2, 4, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 603)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 5, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 70 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 604)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 173 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 605)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 5, 1, 4, 6], ![0, 2, 5, 1, 3, 6], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 606)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 1, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 607)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 1, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 48 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 608)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 124 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 609)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 5, 6, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 121 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 610)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 5, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 15 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 611)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 182 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 612)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 196 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 613)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 61 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 614)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 1, 6, 5, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 6 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 615)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 6, 5, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 21 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 616)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 68 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 617)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 1, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 110 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 618)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 1, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 44 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 619)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 620)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 148 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 621)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 103 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 622)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 171 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 623)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 89 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 624)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 145 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 625)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 3, 4, 5, 1, 6], ![0, 2, 5, 4, 1, 6], ![0, 2, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 175 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 626)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 170 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 627)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 4, 1, 6], ![0, 5, 2, 3, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 628)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 206 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 629)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 123 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 630)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 64 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 631)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 19 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 632)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 45 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 633)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 4, 3, 5, 1, 6], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 1 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 634)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 141 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 635)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 65 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 636)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 183 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 637)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![0, 4, 5, 2, 1, 6], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 638)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![0, 5, 4, 2, 1, 6], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 639)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (512 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 512 ≤ id.val) (hhigh : id.val < 640) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 512)) = true := by
  let j : Fin 128 := ⟨id.val - 512, by omega⟩
  have hsum : 512 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (512 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard004
