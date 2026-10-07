import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard176
open N4R2OuterLeftReplay

-- Cycle fingerprint 015f4de5c6037ab03ae166c7ea72fa528b040fbb14873e9b3d161a200f8af296.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

-- Cycle fingerprint 03df58b17e38567e614e21477670a0d8919b01e0faf87b11e05be65141a9a23f.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2]

-- Cycle fingerprint 05c72d3a2648ef2be7051a4217fea4156aea895fc17572a7d8dc669392ae4e68.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 0a77f7ba8af55bd4bc3b8b92f89b5125e708d6802bd206d09ca8579309ff66ff.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 1]

-- Cycle fingerprint 0d6bfe933babfc8e1fe10451f7a852797524ff03c04228053be71e53e7431d7d.
def localCycle00004 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint 0db22d5a55227934f21f0e54b5fd48b8ab6bd85d5a13c2d8a40d562a0f88bf88.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 19 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 0fb38d187165da73ab3b25ff1e1db7ce94689fef05627167b395fc43f641632a.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 11a5a5df913e23161cb24441fcbd8e953c8a42e87457685ce67276367879344d.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 20 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 13bd53fef4e4e48e6539098bff3d05b94d44e8f9f357d63f3a6ea5fdb286cf89.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 13cfc6c1ef424113de01fe3ff46d62830c7d355135bb0e8a33f566d58001e819.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 6]

-- Cycle fingerprint 14e296cec2911ff41bba39cf91683e6c0a7d640128ea658c7ff371cb1f8895ff.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 185027997e38461fabc24752a0fab9e2b1a0417cff9d41548669e8197ee08f52.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00012 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1abba9554403534f8924d51c559c341aa3e5131d6b453d82674218b4fd1bc6d1.
def localCycle00013 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 1b1cf84b71d93faf8ffbd8e8a823eb71255c4f6ccad61ee46e6da1dfc189d3a8.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1bcbf474a09bcfb1afd7326e69bdff05ab71bd8c961ac0747e83c4e9bdabcb42.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1cd7fe1089c21a80ad07f9a9cd45f805f4ab529f2119e77fa754c2c05d9bd7f3.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 1daddc67ae28533baea0e02e65f22f9e65ad517866f1b81c165d8e4af346f641.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1e9a17bc1442d8644d47f85f798a05d64a705e59360af7b411d20cf7af4d1576.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 3, .corridorLower 1 6]

-- Cycle fingerprint 1ea87b828bfcd9057d890abed50cbafe45222a45e8ecef05816d0b5e534840a7.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 1fd9650831b023a8ddc77a038dccec0cbc0f7981958a08f26b0e240a0cecc349.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 3 0]

-- Cycle fingerprint 2190206f1130c7f28a1a19bb62428c4efd5633d3aa41adc002041a78a4578d13.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 3]
    constant := ![-1, -1, -1, -1, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .gapLower 1 3]

-- Cycle fingerprint 2526a229cf707470781d74d48e39d0da716fd5c5c1629759077cf3faf07fc412.
def localCycle00022 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 5]

-- Cycle fingerprint 264a47e7e7c67bd5c119c3301d8d560e260e207eae72f08de41a887a1ef4d856.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, 0, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint 2712ecca356b374489cd81f7260bb5270d82add2700d91d9e1fc54f8f90a21b5.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 2, .triangle 26 1]

-- Cycle fingerprint 2c3b400b721d1d765c245f63182d471c08ff3b9a9739840687ffc316d5c4871c.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 2f744e89db2db3755747ba8006683e46896f0c29c93fa4e546d2d4ac7a97cc1e.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint 313a53637c700bd5a13f689fbf2d82ce87ce91f029fcd2e1e70c6d64dac4268b.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 344a19efe608f44438524008137103507c34fbaeed9af45e954597a4ee182011.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 2, .triangle 14 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 370dd2452e35e1f87415438b714f8f4491ed0cc7ea4a79aca5c079ff64fd0beb.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3c0a534f2a48e00ea836d24a412aa89448f7eb5d54655c416a3ae0aa288d7c2f.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3d9e706885f9a0113101b76c7b800f72f22afbb689f6224469146e4f7b5ed210.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 415c13d5305580d830b73d20d0749d4bcc7db548172ea78087c27755c943e92d.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint 417661f1dacceac850bc12a5811cc11b717aa817c19583728d7640a13fad1c54.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 42a224722aa30c68332240940b2b321f0599598589e282c139a4d507747e0b6a.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 2 4]

-- Cycle fingerprint 439aedaa0f8c312dcf109202e49c39e745ae6c597dc53ca6c7b3373b81ba01a7.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 49ef7c74beac779d676b8e66341f09f8505bb26614b1b564f55f5acc79af7e2a.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4b3700cf77354d1dc3f19a6b23a56d3e2773f9724228d145996b719ffc9b73bb.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 4d4c20df856f370a98c31ea3c795c37ab66baef3fa0db13ee0b4b731fa767e49.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 4e9c68b4431dc33dc73d10547d21d04aa7d7419f3d786cd652ab8f578731681f.
def localCycle00039 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4f0373d2b03d49ead0182153158bdc6f7598cd47afcfef4eb9f1854d24323df2.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4f16020ee4ee9ff6c0b54ec1c867e03074e18a612f64129935fb2193c5798f3c.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3]
    constant := ![0, -3, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1]

-- Cycle fingerprint 4fad6d8c6e3e593c5ee5f70b7f2ca4c5a28048cf50c8611f4defee85eddebd4e.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![0, 0, 0, 2, -2, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 530d4b4f62499ee859e62a8bba2d1bb328fba4531af138b522b80aebcb5861f6.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5355bd435d86920cfa5b2423b7200af54f4f8a497b55bdaaccdc57986dbc3c5d.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 542dfca87bf42830b3e61aaa6776420ca16da7064e647be743612c66054f707f.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 54cad3bb077402eb554f3a609b757dc053408743c521ae5e6f3c22a549409274.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5575a5ce1a69eac1c9a226869fb1c02a2a0d053de540624dadc8e9d4e73de4fd.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5]
    constant := ![0, -1, -1, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 26 1, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0]

-- Cycle fingerprint 579d3b7fdf1b6445800d0a2871ba433ce1adfb912f6bb9ae7970ea77e2e3a42b.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5b5282c2bf6371132b1978dfb233f9202dc44469affb735775c936d25ef9891f.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, -1, -1, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .gapLower 3 0, .gapLower 3 6]

-- Cycle fingerprint 5bd28d2d8bde46c01291ad149bec97f70ba311a729265bdb74e7386df0b8fc25.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 5d355b6fa67bf2767d34a2b3a033dd225ec75dd300dc4113f7970dee852b9a68.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 5f68e10cc83a0c2882ee89a3a82467bf42e740e786d472352325c7c886e4af4f.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 20 1]

-- Cycle fingerprint 61220ef36db0f8d9b87fb0f78792080a1063546d6a774a32d39a5bf594f81645.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2]

-- Cycle fingerprint 61968ecfcda44d4ed30a1b91aa096c7c93f7be93ed489e283f2be60540f81a3c.
def localCycle00054 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 0 4]
    constant := ![-1, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 12 0]

-- Cycle fingerprint 65940ebc469520762c128bb4c3ca2843219162de1f14b6af484b48484ab66080.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![0, -1, -1, 3, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 16 0, .corridorLower 2 4, .corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 66713a19cb60dbf26e7ac63d0bf3763a3916ec8e2f7b8c231c39820cefe3736f.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 3, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.triangle 19 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 6812f0cb6e6c1a39ac0e4f4f360ac2e68cd22e96432a260c42324029654d0897.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 698b59df1cd291e616ab3b9d513aa72ca38a9bf735b06a7a3b15017f7798f22b.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 6a52ccc76692c0ba55457362cd046c0ce4ce3b8b42b3cd40534c6fd465164841.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1, .triangle 19 2, .gapLower 1 1]

-- Cycle fingerprint 6be6fbbbffff3eaf1c0e5a1a80aad1a63c4dbffeea8386b9d3ce718a02feef2b.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6d391b4d414a44b473fe6c88d7a90437958c3568d429b2d42323edebac7dafe6.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .gapLower 2 3, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00062 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 734c844c0e2edd8c6f5cdb5f76326fe7af0028994d59c51019c67e712e3b4ae2.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 754929658fec57311ba736a58c7a280e05532c300c87711d2c7cefbd83f2c8c2.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 760628292aa8c95b3f7a29ea5b819ee7c25957a5e12bca3c0e9bbc2236dab8f5.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2]
    constant := ![-3, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0]

-- Cycle fingerprint 797952f2e9951441611524e69123a16b685e8e4b2bc30c034bf8cf92ccfde2f8.
def localCycle00066 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 33 1, .gapUpper 5 1, .triangle 20 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 7e209c2563946a7d822350c23123fd2a3ccd31f5408e5afe08445903579347d9.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7f2c8b7d365b64ff7a07534019a8eb51d4eae95cfde1b531d6d23c365faadd1f.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 8018dae29980fabf82c503fae944d81d6078cf238719935aaf16aed14b4c7f45.
def localCycle00069 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 8169b727e266f442ac804b920b0e2e016d8257d81afa7ad8f30f05cdd58d591b.
def localCycle00070 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 846114dc46289a4e5196bd0c2d6371875b9cbfacd1e28568bd814ce09607d795.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, 3, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 19 0, .triangle 25 0]

-- Cycle fingerprint 84d2ef32ee2d9814f0213f46a7f086df7f39a05d5f445edf691fc1c267cbf508.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, 3, 0, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true, true, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 21 2]

-- Cycle fingerprint 84ee06bb87944e2fcefcd05d1f4d765cf5f9683c69dab83fc5b359764a48ff59.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 85106a9b885e860c2ddfda20b14735110e02163a46e1854fd60c117827180243.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 0 5]
    constant := ![-1, -1, -1, 0, -1, -1, -1, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 14 0, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 7 2]

-- Cycle fingerprint 854fbde85cab74443ac0be48e01796f455bfd95e0c9ff8306e4b36597ebf10bf.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint 8a05c5ff108b96bb818ae7ec7b2488f1db7b57f625124f19c2db8e8f6ddc96d5.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 8b5528aa84d8caf927888c711ae6a77847a684cef9f7380ad9f30701e6ac176f.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 8cc6de3f868d64995dff60c6933745ae104e919c283e7aa7f9230f3326c42473.
def localCycle00078 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8ec4fa7afd7cb93cdbd78c86a453deba11643d22047877681224ed343bdf0839.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8f5c74645dd48d27d79cd3360f7593409287b42dc071559353aa2cad851f4c6b.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 91c3cc3f957d89ace063e9c0d5533949f49903b59597bc659f9072194e2a843d.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 3, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 936b97dbad071647b09f52d0b368d1d5d13a3556199bbf00daef07966c901750.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, -1, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 2]

-- Cycle fingerprint 938eb48ee4ecc03a6fe505f0fca4c49bd24242f9956ec85502dc1045c6ac9fb4.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 95859016a3f8977735fe3159561172864828cad1614ad5c64f63c9fe4e674269.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .gapLower 4 0]

-- Cycle fingerprint 95914cd27ea0c6e6f80416db3ec2177b21a1a852f8aa6b0c684a89e01f39b8ac.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 17 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 95ba1c7d2ba9a6ab3f542b0d8d20a8e2095d27ceca7cc1f138502213e2bc6fe0.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 978f887b8c7588760a9ca464f25ca20ca926f99cc0fcae280e8ca5634c25b73e.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 2 5]
    constant := ![-1, -1, 0, -1, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 0 2, .triangle 7 0]

-- Cycle fingerprint 9bc133d6769993b8513ccddcfc7cba59171186df1ec8102001bf109cb51e2206.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9e15d0008cc04a81d3b956e8acfe1aeb53d341077ccd71fdbde8bab21b84a1b3.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9fe323ca1883962b51c32988bb1d5b97938103d2ca2e302422e1526f25b28f1b.
def localCycle00090 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint a091f5771069d6677926b8710f5f8b2f03e2bcb535dd53f928e49bb99e8c2f07.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint a0fe209317a984f5256f41437c837bffff1a32e61ee05dfd6608a0402fb2d5ec.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .triangle 19 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Cycle fingerprint a1a60cc9e92f2f4b5fb29f1b8259da1a8462bd04d16c95fb20a8be2cfd152418.
def localCycle00093 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 33 1, .gapUpper 5 1]

-- Cycle fingerprint a265caca0e40e9bc52f55412795dcda4b0e740de93389ee8e8934d702d48fda6.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint a83b51439383133f1d8a00c1958a7f81748eb92a62c1a9ad1bfc09e03abd70c3.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint ab023c3db10cf7cea684eaec0fd4490f0055320b8d562424cd642c682d44eceb.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ac737d3cb53c044d0d1f70ae35aae530505bc80a196c28feb2fec8c48baab369.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint ae0ea66fe8fc83b85cccd74ef43695c58908898587b9a05b36d3aa8ae82f0a9c.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint aed41837a44397309a6d9e1ca1310277ca05dcb8e32d67984d7c05fa9efff19c.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint aef7a8babe4a0057a8e3e8217b361349c6d68ae2be1cb437e4a0c9192e4c8789.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 20 1]

-- Cycle fingerprint b062de0fadb2f76a5cca4a8cdb79edaac00e69459b5fb90e29c55073ae69f60d.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3]
    constant := ![0, -1, 3, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 19 0]

-- Cycle fingerprint b293ae8d1fa63334d7fa41442120ef5f1ff0a7a3f9bdbd5e4ea41db181836b80.
def localCycle00102 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint b7146b0703bbed67c72a334f861cceda3d38b2a23168836aa9595bcf7927a8dc.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -1, -1, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint ba1f4a80f558c4a698d7e586e50f1a0d85062f7363f78d9c6bce3336db2d028d.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint ba67a18c9056e99135aa45a99d3a806db444b9d1b9c9a1d90b65bcb396e81b65.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint bacf3189e7739e0433c0e84db8fd4552bee9c3f031b98fc6ada1df973a4d6151.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint bb2a1bae2c844d1c05a43da727f98421c6bb830575512760d1ff6a71ea5b08e3.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint bb365390ebffe314d9396d14238f8db38fbb950dd62d3e88cfcacc6e3472ea4f.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 20 1, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint bfe7de5bac737680c32ac9219670a04efba55ad1958574f76bd2faaaf6f5808c.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c0f0a7a638a59726b5b44a6d5623c02119e03de61764202896977d3c140f4a7e.
def localCycle00110 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1]

-- Cycle fingerprint c12d169762436662a36e1a8688e2bfe3c9c416c0e6a949cf65b408a3239158ed.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint c27512d80ebd0e24954f2b92338b708ae4a5b86e732fddc6fc4a79121f134ce7.
def localCycle00112 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint c469861d18c69cd856a61c72040b0b05b4e23af01f42d3c3dbaa67150d15846d.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint c684f5cc43990f29dbbfc2998a18b2505a9c41c9b98b673d3eccff0f0144a6bf.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c6aa93cfb02a665c664a63ee1948470e07fea325cdb13daf6281fcaad4f23471.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c8a400fc9675c4960cbb9424eaeda4b13ec98a73cbf899f1df346d6e0a23f0cd.
def localCycle00116 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c9183f2bdb6ce6c9c7fb5d226cd84a7be886a70df2d43a4f000330fb901772fc.
def localCycle00117 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint c9af448dae04e1dc5b93bb5e08937338d3d1de5fbd07ddb43d076a55cb0fa8d3.
def localCycle00118 : Cycle where
  length := 14
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint ca8cd4b901020d9e4d76b186d77fb7aa42787143054ba6f3bc601730e1e000ba.
def localCycle00119 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2]

-- Cycle fingerprint cb84f473a2b56133e2cbe85a91abd52314551983a2c592bc5670b80d2e3d9e74.
def localCycle00120 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint ce1e21cb66a1df70310111d9363d02f048445a8555391781b8ded11efa4c7d1f.
def localCycle00121 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ce6e1abf79aa021d92ba330e85f531211cd884fd739f128dbd396ed26da25d65.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 1, .triangle 21 0]

-- Cycle fingerprint cfec866d738801343ed305f47708ee5007eda80694d4d6a4033dd5e5477927fc.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1]

-- Cycle fingerprint d099f799c23f84c81d9d1d9c166ab393218734c1e2befb1d2d20aa855e58a87b.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d171f32f8a4e69816aeca81f980e910ff040eee6f32a419710be23b09855e9ed.
def localCycle00125 : Cycle where
  length := 18
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint d3e0658344599c4f5e7337904100e344a8f647abc3e98e2eb97c4dc8576ca8ed.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d41debf1a870c9d806873e34c1e923e93d2bec5d0b6eb7fb34476df47f9f9c0b.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 25 0, .gapLower 3 0]

-- Cycle fingerprint d460a42a8a7c5b2983c883fb488990c18ffd6a8b674d004526a2072d9f656285.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2]

-- Cycle fingerprint d618fd7ccf7948cb3b6c3981ff25735e8592029091834d7cc8c9f31da3074399.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint d66011d4d21cc83bcf0aa7c5ea2742fbb0047bc48c690111796548ccf580dd52.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 20 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint d6956c4d50a7e20bb812798bc9c32a97d8edded57708ae3b8aba4ca8b28b3fcc.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint d76553087feca5c4c1a8ce3eb5ff5af1c3287febc88bbbc641485405703431c4.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d7d6dbfd98279256d07ba1f2b42370a29882305f711d03655434f645e7ea6e16.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 2, .triangle 20 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint d99ce6c7690b8cc589c06f06a3495e3f55555d1ba1ba6a3952b9f93dcbdbc64f.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint d9e23c8a91f8e64c2b4758f30716cea42032b3f58ab24f186b0bcfa187e0b464.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint dc4b7532c38328a9333e943484a87223738043691ecd60a80428d63b4e1f832f.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e033382272861799d04af216f8b551dae46b3dba3d7bcd3fc62f3dbc88ea8ebf.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint e1a8c616942c057b97b3e8d7efa0fa35f305851cc8e4dc79401a8eec6eded215.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ec19815cccfcd092294556d81d47eda0e8c826ba4e2e21642ed69230403d207a.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![0, -2, -2, 3, 0, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true, true, true] }
  origin := ![.triangle 19 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 20 1]

-- Cycle fingerprint eced965704d5465c24c1e7b93b8f907f750f6d6af418e2727d5cc5cc6d24812c.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .triangle 20 1, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint edd183f4d51f91d67ee616be57b90c7b034a602ccaecf2bc5957282dacc98a62.
def localCycle00141 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f0a2c9068b8a3bcf6f4e943b1b575565cf8633dae27baf458dfc0a01db1cc316.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint f2f3c9daddcfb3b6c98cf16eda8ad8203fb76f0f629cf38858ea3bdb6fc7c73c.
def localCycle00143 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint f324ec77e6ed281149de38317b569ec5efa98bbda1ebf5f27eac748acc741064.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint f57dc21467c8e524afc119f416c1fc7183d02f2707d4f315849ffeb2f6e854ac.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 3, .corridorLower 1 3]

-- Cycle fingerprint f6ff2c1d3dba56d8e571934c20795c1814ff1d0deb904a54b45a03a512683fa6.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f72a57a5175c81fb4c2834eaa045777e4eadfe9e24571fe2b703eae3d4c7fddf.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f90a2a9ef7adb571edb5af4331d6f73ca0ad0b2574aad62fabf23fdd624fc324.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f941b59a2c3500af51904da9edffbeb53243762b37769a2c8305d02d1f65ebd4.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fa3555e20d0d207753866dc10678b295635933574bc01636543c2220443e9eaf.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 4, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint fa397ec14157f67cc20f6774733063c3f33b66462dda9ded3663c5527ba2ca86.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint fab327548b3d297f31c86b13d274760ddb97fea8dd3fb0d4ea586fb7aa1210f2.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![0, -2, 0, -2, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 20 1, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1]

-- Cycle fingerprint fb0cfc5fe513e67206eadf5a583a4fdc517ab706d7abd81e2b0bfbc86d8841de.
def localCycle00153 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 7 0, .triangle 26 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint fb5e26fc0a9ac4ecc655477ee993168142d23f4ae77eb414a44c9b66fbfc3948.
def localCycle00154 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint fcc83f7d69002e8eb213dbf27d4f8dc8a6b251c28941babaeaccc11730916ed9.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00156 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fe7afc97d2a25e007275ae2e4cb1e6a3c3db6835c68b70f97e646cfb20cbfbeb.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

def library : Library := fun id => if id < 79 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 59 then (if id < 49 then (if id < 44 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))) else (if id < 54 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)))))) else (if id < 69 then (if id < 64 then (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))))) else (if id < 74 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))))))) else (if id < 118 then (if id < 98 then (if id < 88 then (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 93 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))))) else (if id < 108 then (if id < 103 then (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))))) else (if id < 113 then (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))))) else (if id < 138 then (if id < 128 then (if id < 123 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))))) else (if id < 133 then (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))))) else (if id < 148 then (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 153 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .tail 95 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22528)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 157 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22529)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 105 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22530)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 105 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22531)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 0, 5, 6], ![2, 3, 1, 0, 5, 6], ![1, 2, 0, 3, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22532)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 0, 5, 6], ![2, 3, 1, 0, 6, 5], ![1, 2, 0, 3, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 38 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22533)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .tail 20 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22534)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 74 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22535)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 71 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22536)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 76 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22537)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 136 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22538)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 5, 6], ![1, 2, 0, 3, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .low (![65, 117, 104, 36, 7, 9, 58, 139, 152, 110, 110, 110, 23, 130, 137, 63, 143, 59, 32, 150, 120, 140, 77, 154, 10, 12, 10, 52]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22539)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 6, 5], ![1, 2, 0, 3, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 31 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22540)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .low (![65, 117, 104, 36, 7, 9, 58, 139, 152, 86, 110, 110, 23, 130, 137, 63, 143, 59, 0, 150, 120, 140, 77, 154, 145, 12, 10, 52]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22541)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 28 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22542)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 73 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22543)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low (![155, 117, 104, 46, 62, 22, 8, 5, 94, 94, 94, 94, 37, 133, 128, 146, 107, 108, 97, 144, 70, 44, 68, 90, 153, 156, 85, 42]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22544)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![1, 2, 0, 3, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 132 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22545)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![1, 2, 0, 3, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 51 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22546)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .tail 132 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22547)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 61 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22548)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 45 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22549)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 45 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22550)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![1, 2, 0, 3, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22551)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![1, 2, 0, 3, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 6 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22552)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 3, 5, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 0, 6, 3, 4], ![1, 2, 0, 5, 3, 4]], proof := .tail 80 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22553)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 0, 3, 4]], proof := .tail 30 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22554)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .tail 87 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22555)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 2, 6, 5, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 98 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22556)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 3, 6, 5, 2, 1], ![4, 3, 6, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 142 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22557)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 29 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22558)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 124 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22559)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 111 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22560)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 114 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22561)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 88 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22562)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 78 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22563)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 49 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22564)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 0, 4]], proof := .tail 16 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22565)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 29 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22566)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 124 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22567)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 73 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22568)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 114 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22569)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 103 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22570)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 27 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22571)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 127 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22572)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 0, 4]], proof := .tail 115 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22573)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 101 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22574)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 56 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22575)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 0, 4]], proof := .tail 55 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22576)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 69 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22577)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 124 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22578)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 101 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22579)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 138 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22580)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 102 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22581)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 149 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22582)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .low (![155, 117, 41, 112, 75, 26, 8, 72, 94, 94, 93, 94, 37, 123, 66, 93, 113, 3, 66, 93, 35, 153, 93, 13, 18, 93, 93, 122]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22583)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 64 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22584)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 114 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22585)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 25 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22586)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 127 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22587)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 2, 6, 5, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 98 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22588)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 45 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22589)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 135 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22590)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 116 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22591)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 3, 6, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 142 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22592)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 60 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22593)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 6, 3, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 4, 6, 1, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 2 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22594)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 3, 6, 1, 5, 0], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 21 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22595)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 6, 3, 5, 2, 1], ![4, 6, 3, 2, 5, 0], ![4, 6, 3, 1, 5, 0], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 34 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22596)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 67 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22597)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 151 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22598)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 1 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22599)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 84 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22600)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 40 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22601)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 15 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22602)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 54 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22603)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 3, 4, 0]], proof := .tail 134 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22604)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 79 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22605)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 39 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22606)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 99 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22607)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 67 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22608)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 121 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22609)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 50 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22610)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 148 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22611)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 106 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22612)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 14 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22613)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 82 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22614)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 0, 5], ![1, 6, 3, 2, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 24 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22615)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 73 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22616)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 56 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22617)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 4, 2, 0]], proof := .tail 53 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22618)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 81 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22619)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 3, 2, 4, 0]], proof := .tail 55 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22620)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 40 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22621)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 109 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22622)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 118 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22623)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 11 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22624)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 89 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22625)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 48 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22626)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 6, 5, 0], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 3, 4, 0]], proof := .tail 91 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22627)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 67 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22628)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 121 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22629)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 50 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22630)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 148 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22631)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 106 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22632)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 119 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22633)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 82 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22634)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 0, 5], ![1, 6, 3, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 47 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22635)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 19 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22636)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 148 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22637)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 33 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22638)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 131 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22639)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 92 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22640)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 125 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22641)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 149 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22642)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 3, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 17 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22643)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 4, 6, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 4 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22644)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 4, 6, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 83 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22645)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 96 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22646)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![2, 6, 4, 3, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 100 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22647)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 57 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22648)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 4, 3, 5, 0], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 141 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22649)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 147 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22650)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![6, 2, 4, 3, 5, 0], ![6, 1, 4, 3, 5, 0], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 129 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22651)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 3, 6, 5, 0], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 81 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22652)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 3, 6, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 25 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22653)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 2, 6, 3, 5, 0], ![4, 1, 6, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 45 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22654)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 3, 5, 2, 1], ![4, 6, 2, 3, 5, 0], ![4, 6, 1, 3, 5, 0], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 1, 2, 0, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 60 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22655)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (22528 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 22528 ≤ id.val) (hhigh : id.val < 22656) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 22528)) = true := by
  let j : Fin 128 := ⟨id.val - 22528, by omega⟩
  have hsum : 22528 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (22528 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard176
