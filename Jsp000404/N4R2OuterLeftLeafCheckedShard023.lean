import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard023
open N4R2OuterLeftReplay

-- Cycle fingerprint 000dd8a23d7a09303bf55136b7fa09959c636739bc516003b076f04b89fbfc88.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 00f85653fed483a1b1a6a17d7ee49ab964d22c47de5582da1a9f28cb1b521241.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 00fc603924155497060ab7cdbc82e19deee5a3450c7ac7b2283dc73e0573fa1a.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 02ec389b3c7ba3fcbd5eb0ee5a1fa65ee42da7038b90fdc8467f20c5ff222046.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 03f7ac870d26a8686894dc38a883ea61fe764b41e7b0afce2acf4d04664ceec6.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 0567549c08b0095ea2b3b12445efa08e1fc77398c6120f9867cbeefcff3074ff.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0611b0b6cd563623eb224ec84cbabe8c83591210f5fe1736f1e27681d6d038b0.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 06249ffcbb2bc23e04359a0b10032478830755a252934c76ff66272f74759273.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3]
    constant := ![0, -3, 0, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00008 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 08e981218163a0e28e04c3ec13d54613b568252b43e7733dafa9df43e4f0744e.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0a41f02e8ee1cffb46936bd690e1505fbbce69ef08795481358c71f51ca8bbb7.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 15 0, .triangle 26 0]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00011 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0ea2bc1235f716e36b2846a05daf49daee4ded481efe9157b64ffb5e76e4c2d4.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4]

-- Cycle fingerprint 0ef393964cd49a072133accba5e03b4b3a5ab12adb46f20b87cc1c5102feb36d.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 0f5acee1bcf8d7d7d25ec1884a420678fb99fc577173de2c35e4d3af6c2654cb.
def localCycle00014 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .gapLower 6 2, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 11045ccc97c1645505d5312dd9fecaf5fc14a2ffe474b16bab1616b1ccd43087.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 121aa9f8502206a58dbb24d8252eed57a6f0b594d7406b2d33cd0d94a2fab6af.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 15ea8db3858ea95801078b9f104a4c3f1b25c65f3d2bd0fd69ed5a6d1e4e4390.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 168dc00279a4dadd2e891bf310468eebb065eb4d9d5b21f120501c00733190ae.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 172c4f7481207d7c9e0f6c940f81fa100f4e5c7d7f252e456c906bc2dd5247b1.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 174ae4beae2d9e20e73862a9ea70b2cafb792de60539bebc8fbb4ea64e84ab05.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 17cf5bbf3fec3c6fb0a570fd05edd5b98e59f2080abbfeb029cbd9c7ad250692.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 24 0]

-- Cycle fingerprint 1af6660d60f65af8e5901b0f5488e9922f9134481c6910af75b8eb59c7450c93.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 1b0f15d20b6e7b795cdcb2dca30080376be6908d3049fce1ceb6d2473df1e342.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1c1a9212ab5394d3a732106a114733458a0d4324de2a051b40990e7fbff74050.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -1, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 1d2938958239ccdc44a2b9513f673f5f08934b578c4af0f138bf2ec252b17a83.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 1dbeedf275e1ae1119d8159edc8ab4b951843d76ed7fc9df62cd0ed0e69ede65.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 2052f118b84c97d8ea6ab55cf24e4c0f2594b0caf99218646fb646d0b3cd5c2b.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 209fbf3b5c39dc2c953407f6515ed400a0b6f4fb4114e6b692eb483ed1fd7832.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00031 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 22f57b40f11af6e442bc9068c570ae63da98a21bfc6d6258c02894e60bc6a67c.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 2380b54ea8c41653dd484c9b8db229ffb89bb41b41089363115b5a85ff271bea.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 238d200ffe99e679d3cb48086f3ca05d9a5f7269fd24a0bcdcccb6d450de67e7.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2489359457ccb53dea061f1de7f57660705b25362b4f83a38c98bf89867bdb26.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 2651259092793db88212e81b4e1ffe309341794f339eddb31627acfda3781feb.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 2654b7dad0793b8bb31a9d297494969ae9064601338bdefe05098497757ef7ed.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, 0, -1, 0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2703e0080e5b0bf3bf26b5691ce78b863be900e83198b769bbdaf73fdc0d991f.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 2755fa0d51f331a44944bc3503bc3790c58632177c658c8fd04dfbea4d745a36.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 276fee3267b4477f54aa680277f99efb8e3d0a126f0e805b42e8b238240b6a46.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2799b55bdc58b29a3fed7571d2df2c89cb18b52e02d65d85b20a247e2da45b21.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 279f099ff09bcb5884005d8ea5db9d99d3c19e0ad74d3d48564c41cab3aff6a6.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3]
    constant := ![0, 0, -1, -1, -1, 0, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 2879a9ea282335b74ff44a5eda221018ea7637cf0b252e7b5496769b01dcb2c5.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 28c6e462108f1e9a903544e066d5d14f661018b7e9c27649af99b9f81b708627.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .gapLower 6 4, .triangle 21 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 28db2d48469496830c523a3b9a3a2174dbd009e0dce30c8791bcee645ec4bd70.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2981ab2275c699ac69cc37d2c09c1a96b7f13026de7920db46d1aaa210c48586.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 29f523a73dc0dd011697371eb87963440e14706c4b9dbf88272a701b46c17a13.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 2a84e0af2bddc83de40dadfb29288a1c6bf05493b81766d6d51c9756dacad159.
def localCycle00050 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 2b117f30ea7a3b00addede946ea8704982ab1e7d869c13c5666595a802be0be1.
def localCycle00051 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 6 3, .triangle 18 0]

-- Cycle fingerprint 2bc372b4dfcab36b3d4582c4613738da2e8ce6633423be77eb6d4be1ad14192e.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2cb4de23f4f56609cb1c5390c5b0f8595067c55fbd68b4b75ca7c778d32b825e.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 33 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2d3fa5b943b6e170d318be568d1c91627709a2fd81688836b012d013e4e0fe25.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 31874cf39f9b1c00bdd089045c1fae95edaad56004186ca005ea01ed74157506.
def localCycle00056 : Cycle where
  length := 14
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 3, 0, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint 319ade4afd00daf1ff700f224ab91e2e6772b1a7eab0b4572cb1ad195ff69316.
def localCycle00057 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 32e15e3230745da6cba2915ab6971351fc19ca4d8a7c526f04c547ccba36e8c4.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3441c9faab954f73750b0ac25a6235329f6d98a730081560025dca7145f38f15.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -1, 0, -1, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, true, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 9 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 349c8ebd262bab22065838587466fa9b7a1765a383b0ead08762cb083e3b8c0b.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 34de1fa4dd65850acb9685e14a88f2002147647ca7e646e7459b39c2ecbc0c28.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![0, 0, -1, 3, 0, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 2, .triangle 10 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 1 3]

-- Cycle fingerprint 36d9559ba100fc0be2a8cf42feb63f7a970b4189b5df917d775efc209052b3af.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 374cf1c3806f43f7ebd92e811e9e0274344af734e1cccd75b1d39feb067cc6bb.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 396ba739cacf001bf95415978c5c38f764e67046590098192d392475ee250301.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3bdb2d339558ba52902d4e4916654fc9e3370fc341b1326bf3eb6f9d3555f1f5.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3c833a13860087050cfb810e59c41ac69fc6c25e3606d9a042bf1960653c6294.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint 3cbc9a3929176f34e5df7f77f560ce02c61d838529f936284566ed3f10063471.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 3cec7ebf7a45414217e093be2806b1b3ebd0f5b0c20ffae5882a87c6eef29f34.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2]

-- Cycle fingerprint 3dbe551122f8947322f827df98068866c44f1067cdba1c21cf383ef2ed742ac8.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 3ec3f5a987447352cfc09693602e2ed583adf4dd026947f35224f164fae58736.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3ed34bd805db38b4c33549ec8645977c579b494e8b0ee326778123b70b5a4297.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 14 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint 3fce33f0a4ef6d2ed42b85353910300024b71bce38fe09901120ece5ccf5628b.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 400dd31ed319a3bb34277eab81d77285f9cd43fc286b1a91006819a89f0f62de.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 403acd645388eec2bf3a7a315e0c12b196c808eb7252c12e5aa7d7381163082a.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 405500cb3fa4f4e603a8820831902e568782afd487989ac0348c6331d609b858.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 7 0, .triangle 0 1]

-- Cycle fingerprint 4219a05814635ce89b578de91f2aa1774cf5e20f83fbe3ce05e9b33ec356378d.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 443563070970df43959f2e926746a3c9f5f722341af3b2bf27803e37e676bd41.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 448df974faa3d439b38045ef21dae422072eba09c88373f2ace027a45067f301.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 453ec21d52db14ddfd6efb47cc4b1d0c697b34525147869a5612c31560f8ebf7.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint 467a6c76321deaf4f9713386e2d75586ea040becb9361c8057a7ad187aa7a759.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4827cc05af1f0ae1a24a2f33cbf9b72621c08880ab3a08033f9ee40a501cad08.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 484e10b11def51e121e01adce62c77538e34d4e72b3c5b49517b929a744c410b.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 5]
    constant := ![0, -1, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 28 1, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 18 0, .triangle 27 1, .triangle 26 2]

-- Cycle fingerprint 4a0ad45d7f8e00ceb7a85346467493ef4e955cd76f0531e6c23a08693859c2ed.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 4a89c7c97e813c715424c4690d8ff6ebee9c45a314ca966efe9d426d24969f30.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .triangle 17 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4b5dd22ad1b5c11f1669ccc483c98535c32d44ca4e183bd1ca6b50737df98e56.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 4b83ee833fb570453d86298d3c43763f54bc50fe1b2e65e208d2fe5b79f31892.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 4c23ed7991c41ec513820d97fce9ecb06453ec8498dfbb8ef11ab15579e4bc3c.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4c3a4f8f1142b0282d9f13984be4a5807475b3d3a5d73376461b9d37f12b8c57.
def localCycle00089 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 4d078b6ec318d0a952b34f6cf2919256bd08bf0e6f3524813f767ec818b1a1ce.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4f752aea4593c0666e28adc4c0620818bc9acad616e5d9b1fa659e66500728c0.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 50a76d2bb01e85381c09072e5797636937b53d1757e4a01afe5315bb1b9f464a.
def localCycle00094 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 50d9287209a872dcb58ad199223c71e09ca1bb039b51f894862d4e00922714c1.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 50d9be438903ddb98e1ac90f78d432ee6a701acff3e02cf189ab7ef03cc48794.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 11 1, .triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 50ff39a545a749802b010675704d52e6640d008e663e343f5ae2598647bc7414.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 533b6ca70f330e41cfefb85aa914ab62e9f73a08e7d1969255fb952fee976544.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, -1, 0, 0, 0, 1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false] }
  origin := ![.triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 54ca3878f49c2bd843547607fa2cb44ba4a02d6a7a200b2f34d8fdb8385c02ca.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 54dea8d8c0cfed57067894239b1b0b11b5b99a433681c85090e46e96c21d42b6.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 553a0730f2d5a52e5899fe10cb6801c379396ef82b0a02b7a1a5714435fdb317.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 16 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00102 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 56a7b865dbe43174ce3093725a12270ed52192212929678061ba3a9c5c381242.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3]

-- Cycle fingerprint 57825300d478ad09418897217b8bd51e90f0eafd906519f5a534c81b958d4035.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 22 2, .triangle 24 0]

-- Cycle fingerprint 58c0bf72641e937f6434982edf41c3ee1cd449926058e77bfbd5467fe99c091d.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![0, -1, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00107 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 606f07878008c78de53138b2c5e66e356665e1ea249dddbfa301a6223580e11c.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 6091a3a394d934954ed3b0ce8e42dc24f5dd8930bcc8dcb45f347e1b8a54eec8.
def localCycle00110 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 6133f5c48a560a63a77d0f7325359c386788a51fc3d99a64d62e6efb9b8e1653.
def localCycle00112 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![0, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 22 1, .gapUpper 4 4, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 6136f2927f79c6b4819fda4412981dd99b3a59a9334d7cf77c146479872f5a50.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 649edb8d9f099b186c54547312900a32b758ac9dd3e76ec11f5a2ca245d58084.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00115 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 681330ead61f432c75a985a3dd894defad532caa888d101b9ead040a9df1dc98.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![0, 0, -1, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 695d79c2a59a494b18ef7e0f128256efb4acd013ef072ede96ccb678e7c0f503.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint 6a1864bef040aee89c04787d7bb11d74c68e37fd3016cf98a071d9f28af07a1c.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 6a8acde7fe61cd4c6834b10be531d3aeb4dacba55472c911c4abb70f2d78b94c.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 6c39265ed5df6338db8f76a40e769381c2824304e847d7a8f5fa94e2d40bf93f.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint 6da671d9086a82c813da16a4650b4a1c9d7f8700a6525e5e6c250831d58cbe60.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6dea7ea444f48258e26d9f0bb94f6101c67e9abb8d64c97011e3aa12cc307c15.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 6e362879184b2543283eab5d8dddfea666378684897b58c7de5e6a4c160069d7.
def localCycle00123 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 6f2011dedde377042708bfc6835f6679eacef343c4f70b600d621a093ba84996.
def localCycle00124 : Cycle where
  length := 15
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, -1, 0, 3, 0, 0, -1, -1, 0, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 7004a767536840e8cb2d8183b3775e0aa63b2ed848716b1a1190fdcb38dfc996.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 7189f9163d9b0fdeb41b999367006896af65036a4d64655a356a009268f2c65d.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, -3, 0, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 7277df3bc52ce3ba4fcf1c9e5cd17b8d6dcee7a43ddd21f19821a70bf3a265ae.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 732be887b54820cd414fe70975a0b4894ce975bc003cba0bb17ec170d9b8c155.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 786c56090b0f94fe60ab615e72b384e33270d08b16d0e582b752df215ae23c73.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 787daae483500008454fdb5cc94bde0d17d2dd6568984d2ef1386c1091bb9e37.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint 794623e23f7876d2cea9b398baec81a95af9e03fc49512ce49b7533ca585e5b6.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 7975415da0749145e480215e2ce38030f752df178c0b572c15b6792e5c602475.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, 0, -1, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2]

-- Cycle fingerprint 79a1410eedb1a38bdb16973276c854616ae399911bb90829cadbd96dfb48e1ea.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 7a09075281b67dba3355668d0d06894ca6dedab756edcd5969d463914f0480a4.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7a2036e2a1267a39b6dedee4c33297f7efc1fb317413bf260488124bc2149435.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7c8d500fd6af7bdb36a297fcb7a569e4479911548b95300a4d3e562c14f53839.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7de15d6de6c703ebea1261894f6aab40e86a7389e9d0d318655bfef40820fddf.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 17 0]

-- Cycle fingerprint 7de9fe481aa6220c5bc6ab3375d27c555fcf4646f57baabe18a5695104c78f2c.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 6 0]

-- Cycle fingerprint 7e243d04fe835e8fab2662693f27a34f052d337120e445302aa900f4caa4d0d7.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 7f184b8638af9fe385932b3a7bfa65df07dcf4f2822fe28f7cd15a1bd9e3bca9.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -1, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 8030155a32f6a919eeca98d59cfa75ef631ef344c0e5f7c1bcf9a3321320eff3.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 84dbd38d61fc03413c7160d159f37e8710f21e5f47cdb1de76142dbd91d4d8cd.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 84eded6533dd9ee694aaaab70da2632b95b395b23772de7b3eb3ac9d2252db85.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 855250c37c20b5f38102d4507362407cce51733deb044b96ad849fd82dd7dd5d.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .gapLower 2 1]

-- Cycle fingerprint 86171dae3bc45d16c068321d6610e2c6d5bb4d50cde5c113eba318ee502e710a.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -1, 0, -1, 0, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, true, false] }
  origin := ![.triangle 2 2, .triangle 9 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5]

-- Cycle fingerprint 86687ee51148f06cf2b189637bcc9b48aee9aa8299cff8456ea783e1980c9a8a.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 86ec0aa2e1e6f72b37acb0eca1bb9c957bafddf26019074fcda5264395768dfe.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 88e21bcfbf8eb6b6a0696bf476aec8b575ea2f09c1d91fbff6116883e0084813.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00152 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8abf9080993e8ab61535589fed7956d36e40db3f72c3e1dbf3c1851ed336ee1e.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 4 5]
    constant := ![-1, 0, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 9 1, .triangle 31 0]

-- Cycle fingerprint 8b59e6335d561639ab54c07bc2cd603734a1bdb3f4085e0b3a9122a0892ac4e8.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 24 1, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8baa5b47b51c22ae6c6e0f384e39e5c3529cd3132961d4fcc2d2961e1ed97cd2.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00157 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8d75599d7c07b21b98b2d287b1e918ee16d11210a70b4721dbe380541425379e.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 8e530950249fd7b8c9e3296a14ff730eddda42ca653a4466decc11734e5dc794.
def localCycle00159 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 8e99ddb6947d25b9043012d5fee6a82e73cdf585c3063b30739900261bfdd335.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 8f8e5a49f9e55ab9fe46d240c9d9fa36ee467d8d91de34eeaf910c30d33b41be.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 91665d6801168d5eb12b18a33b4949b8e471f2cafb85040071b347a796a9fd98.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 91675553f08df58c66e78dd48e6c462a85367ef7cc2105c9712033a56667ded6.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 91bc19565844ade036fd4e27b8758bde9fca52ea0e67379a95afb45bc7b71ce9.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 91ca9a132ac2dbece3f3c77e0d732c968e0fb3c1825b92c3b74403af0c636ec3.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, -1, 0, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, true, true, true, false, false, true] }
  origin := ![.triangle 11 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2]

-- Cycle fingerprint 94071fbb62ffb0fb71d1a860499e4f7c7356e266e168f1e4456312c9a07dfbae.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9440c5ab6840332372b212a9f3c46c343861857e69dba4402f58cfb54d2f87da.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 9449d5624757fbb836dc121971b8c03c9b3cd8eb7ea5d54d6e439c489c0a44d3.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 947cd2dff4828e071242453437ea46ef75c68e90c98cc6798a8c8839c2b55cfe.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00170 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 96caf805e6f478490138dbc92e09376bc035d2c073a102e3206c2b032816ab51.
def localCycle00171 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 97038eea04441670f91e88eb7f3a9ae5eb5285c159e22dc4bcaef419332937c3.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 9776a3a6e1297caaa9d934d782bc3a7a5dd0c22a359667846fea6ab6b50c5fb2.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 97820f4e3286331e9c2cc0ec7fba136ef82e3eafe79d070cc5832694b45dccd8.
def localCycle00174 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00176 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 994a7646d6a1be00b8f14a3b925b5f879986060143a1308160a8d37ff52d961c.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 99600781ac5bfbaaca0de997ea3248593cdc3d5bc0054e27c4247dabbbf0ea23.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9a773f376873d020d078440c71dc9e4a1861a483a60bc08276eb1a892aeebb07.
def localCycle00179 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, -1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 9a7ebf9198555754c79c448cf2236a3cf9461bfb1ff6234e38c6358fb53786d5.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 9bd8b1a66be5321164bd30576175282e17bec4f53243a2fd37cb1ed78dc2dad9.
def localCycle00181 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 16 1, .triangle 6 0]

-- Cycle fingerprint 9c9cf7b56012bf0f338aeb954602ff5e2aa5024a62d6cd178a5a02cc5b1e0f78.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9cf73b6b1ff487ef9b6c1756b14f1f3863bfcf8463087fc6bddaaf2bc7f44162.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9d3e2d5289cc53da5906bdf002a04d259157584292927e652ac4073398f30254.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 26 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 17 0]

-- Cycle fingerprint 9d49e2086430758a52dfe0da4fcc25c58d38fff138c548ca054cff038d8c5579.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9d85feceb09cd5509ebfa5bb3647d8cfb6ebc1351a84e20e608b661f3f9bfab5.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapUpper 2 2, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0, .triangle 16 2]

-- Cycle fingerprint 9e1e1c7cdcd7154368a4aefe94425a21d7ba0a0ca4836ea753d24c83b6aac405.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .gapLower 1 4, .triangle 1 0]

-- Cycle fingerprint a18d3e52b9966216309e19a014a486343d9b119fb7e04b1843d18436f094da2d.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint a38607f08b8cefb570b544e8d0dcc8d13647e79d9ac0cdac325b20b9a2ad678d.
def localCycle00189 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint a3dfa395fef333ee966e8859e56aef1977d6ee911e5155580c45bd9aca19fe27.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint a4ac8e5f2c4d37f8367bce93ac23a664869255c7a1b17dc23aa89067ba969099.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 18 1, .triangle 15 0, .triangle 26 0]

-- Cycle fingerprint a6473b90651453fe1e7b4f7532d72de8aea5d35712e52c2920f316206495fb74.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ab18c40d4cb6e2eaaaca33ecd6603fa6da4386d36ec65f465d4ec3ca945e2d37.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint abf305556cd316f59b20462bcc1ea5959dfc947773ba3fda6cc7a639e7f6c45e.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 4, .distance 4 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 0, 2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 22 1, .gapUpper 4 4, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint ac5853d4f673f27035138f76f99e36c60e1b4f06ed83f86c242ac363f122375d.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint acfcbea79ea2df248cd472217b71459716471f582079ab0cd705d2e831078961.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00199 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint afc5b59d3fa7ab56fc1170d87b7c81bbb0591f0e1a318155e5e9a678bbd88a08.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00201 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b301bbf4a5f52ee1ed31092102f30e865257f0812989b04f1d41ed658b79db12.
def localCycle00203 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b51212c15174ae7ab80fb4090785eae29a297c4d31c8c9ce8d03a308979b0371.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b559e02593a38d9bed582eb7184cbe7ff7a3cfb7b6a69d15a9fa0ed5408e90a0.
def localCycle00207 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00208 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b7ef812ea580f748495028786b53f2b692bc7a437caec600c0b7f484e47c7a7d.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b8add20e989d34c73c657c58bb3f27c3e01ac2e44fa82b739fffd54296678248.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b8df72b8a7dd652e7113c98798ae7653a52ce4a408e978e06f59033d8bb74f2c.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint bb7249eb6c10e3dc1cc5210d61e58180156c5bf97d65269f0a20bbf6d851ab97.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint bd3327ed805cf48e01bf80a879545446bf1a730d5ffd9970fd68825b28e2c6a4.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c1802d3cff738f6d199fca8c3b8c0929d87cd138107b0d9a4ea1a29e601b4222.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint c25a2b7318a16060a079731494cd7ed4487639d09f0f1db8332827fd1458008c.
def localCycle00217 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c2dedc4d6c796215fc083589462166de5526900333910fb922fb557785e0093c.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c523925cec2a96bc8c4570346ed39c0bcd9ededffa5d27633b994334c25a4667.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c54ddd8ff40bc848551e1ee92b9f43d21fd4c8c43d6a7751e104c52d7f919b11.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c5fcfee85447095ca6307e251d8936a1182e055f305628a1a4a6fdbc373cd6a9.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00223 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c6a9f99dd461038f4f56d0c824aa157885f099af7ca137d9aa816e94c1bd9fd6.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, 0, -1, 0, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, true, false, true, false, true, false] }
  origin := ![.triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0]

-- Cycle fingerprint c82d056eda0720f32cf7fcb93b85c6cf5fab6d0d9ad33920eca8b6e699834269.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c920072ec595f9f208e0af2153aa38bb05591c3f6032a4e9e44fc7e0b211aa69.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c92291c805e47eb266126a768eeec92b633e2775103f1a4de980543141a8cdc3.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint cb3a12bf9ef078c3e889b761e5055a1ecfddb176ac7980e9683218e5fdfa4852.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 22 2]

-- Cycle fingerprint cb4a20e41896ac38bc7530538c88fd912d3474b17aaff2acb238ca68b2be72f5.
def localCycle00229 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cc661757948d3264df9a0d99750e4a5bbf1a56ebd7fedd333428c92b7fd7246c.
def localCycle00230 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint cca611d671674bd64c991cffa5103260b7cc1b10c0b19f5df33411991617a12e.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint ccb9bc5fd4dc8fac2d295e1f3897ab65b99b15ff9c512abeb0860074a0798c40.
def localCycle00232 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .triangle 23 2, .gapLower 1 4, .triangle 20 2]

-- Cycle fingerprint d15c68dc1a4d097d1277e54b7f8f04bf346d7eecf020aa6c752154d85757b9d1.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4]

-- Cycle fingerprint d1c4b01732f7ba71383d0c47619e73e98794cb6410fa019b6770622046c00d32.
def localCycle00234 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d2eda2961e6b837c8bc631cb2b250b485e842aec67fb191c54f05e1afb8cd421.
def localCycle00235 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint d4d9727772551381b138fe0483b14b7b3d72af96192bb07cebc4ed24e742d97f.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d7c5f749b3738d5f089ba089ee1cfc0abe06867057cc77d1736f4d8e990c64b6.
def localCycle00237 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 15 1]

-- Cycle fingerprint d83e9ce89d5b9eeea7a6b5d0eceb0bb4c1b108cdcc9549659e3d58dd5160b15a.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d9a3c14f35450f92b6881056213d79c996ab0f808f350939ff1e96a75af2df66.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint da0f6305222bc8ac7e44e13aa686251b9312585ebeaf487763fe983f4899867d.
def localCycle00240 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint da4e9d9a4e3591d9192a13e1375f96133caa27410e8460f7f9f98c90dc3634c2.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint db50cb21964ee201ad2577272d306bc234bda0327e03b92dd9d5a5c88c22cf7a.
def localCycle00242 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint dbd36b0513e77eaa028df48c3ec3c3a5b32142fb8991b6b8b0f5783814e40a67.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5]
    constant := ![0, -1, 0, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 10 0]

-- Cycle fingerprint dbd70184b9cd5fc44fbd3f55b5c7c7c64f33cbf7efe4bc239a16f0016df242ee.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint dbde3065a8ff7a4f531371977eebeebdf89cc329d785488b0e27fbc609f31c63.
def localCycle00245 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ddabc5da9370d143adfd7b25765da29bff6744ac521207ef679d2c42e75e88dc.
def localCycle00246 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint ddbc05f1799ef305b0a7723e8af3b6dc95b37a1755f86aa292ebde88b10416d0.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 16 1, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint de708bbc3fd2cf595e9c1d98ee7431dd0aa52b7e77b0398e237f9a04a5be5eba.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint dea88723e1289d4ff0d62b6be8dd4a22b9d5123811c232e523604947c7ee4c2b.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 10 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 3 2]

-- Cycle fingerprint deb1f55ba4bd2bd35ec112b5567fc119f8e882ae46544e58f4c39d5b7c721215.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3]

-- Cycle fingerprint e048baebd629bf2841cf74d8381e4ecfcd1d71341094d2ff6e1be39bb1da982b.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e0806dd01ab08bf5df83b29d722d5fffa1d4c9dba9af8721513112e2ce4690fd.
def localCycle00252 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, true, true, false, true] }
  origin := ![.triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint e220c5c5c980978cb199e67a490e90ec21701b1e6b09982f48791881616cba52.
def localCycle00253 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00254 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e43ebade6b477659f9b967bcd6f32623d5f9ddf27e32f6cfbb92aa6282cdb598.
def localCycle00255 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e45284e84e6651fec95ba65fc7d9e2596564aa0ae69f2bea1bbdf9907218e1e4.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint e46c218b1a8272ef55eca8bf7a5ad33846462d5283c48ba3c57069063b5bd964.
def localCycle00257 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e525389d75c6702ce3ab208c18f0f1e327306ed61a6dd09fbe26ffdf70f14a88.
def localCycle00258 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, -2, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 2, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint e5846869489d0e4eaca3f1d43500bcc36ca973d0e4ac6a8c79330f477ef04af2.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e81706872f88096a8053800aef35de9042a9d30d8eb9d3db6e416894701762e8.
def localCycle00260 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint e886e3ff718d69a6a21ffe7fae0f90d5c7d5d6fe0f556187a989792b46e7bcd8.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e974ae83836ed96b39898aaefaae8adf72b633d4a7a3ec9ae1135e6db175de7a.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e984789e413552df22791401367d2490383f124f2c6efd1053cc2089cf96e354.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ead35f80626fcc88d48fdc6d3d6f6c35aa79602523ffdf0efb55f3ceae9ff875.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 0 0]

-- Cycle fingerprint eb7391bdcd1fc4ad01c46036c14f3eef27bdbf53ca7a15db5a372e46cba5f4b5.
def localCycle00265 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint ed30e46151324b77877b19eadd9092925eb02a7bed9f12f4cf261d54aae673ee.
def localCycle00266 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint ee1854332480d5b058bf3b8278bbc7aeafaecc4696cf3820a78192e15172fa9a.
def localCycle00267 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6]
    constant := ![-1, -1, 3, 0, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 33 0, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 12 2, .triangle 14 0]

-- Cycle fingerprint ee8b2204afd77912b49cc422559baf882ed9092fa26212e07f1f373768bb2163.
def localCycle00268 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint eeeb6302e9d8ca5491df1132d9672fff2afdb81749ab0ce8af58a72d37b57212.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint ef1422c527f95926ec1b573e68cb45dabbe328bb7c649b8d07987fc310d64097.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint ef78bb454412eb30468f7211a778be055ca99c9b088f2c7e8eee3945ec169a4c.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f0fd925e7a63a348f64472b30980657efc72a252ecd4707731acd5947c614b42.
def localCycle00272 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f13de0f3e2ce5517725d21e5d9134dee210fee5fe0d60c0862c77b1a93849194.
def localCycle00273 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f3fb1e1b3d33f8a71823852a180f3eebe781932c2059afda8a4c6d95053dd0e2.
def localCycle00274 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint f415e2377affca08d00a8acf6fd3abed2e428ffa69d8129f1aabd9f73fc7ebf6.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint f6cfefa5777a35febf66ea18082ce567376087b5526918aa4264a8e335e62c97.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, 0, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 2 2, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint f7264cb87561645ea2db0eb2cc16a6a5189978f9145e8f38f857b2651af96659.
def localCycle00277 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint f7426e7ede10dc413047f0b35f4c49ecb00695e45beddd2750ad633b13642d8b.
def localCycle00278 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f7da6d28293cc001b2555acb13a055030f7651ac95a2bb5700f4ec96358925ea.
def localCycle00279 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 17 2]

-- Cycle fingerprint fa15194f52beb93a13b3cd41f85cc206e11843c9ca5209000ffd5d41c7cea714.
def localCycle00280 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint fa67e861a470be225e3861f568edeb2c348b87cb38e6d44cd5051fc47757664d.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00282 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fbbf09bdf4d150460e9560154bca5daaa67d87296edfb3de3084a604f751dfae.
def localCycle00283 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint ff0ac10f60e5fe72938d925ada18dce19870247254fff174500b148e4a855482.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 17 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

def library : Library := fun id => if id < 142 then (if id < 71 then (if id < 35 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 26 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))))) else (if id < 30 then (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))))) else (if id < 53 then (if id < 44 then (if id < 39 then (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))) else (if id < 48 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))))) else (if id < 62 then (if id < 57 then (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))) else (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 66 then (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))))) else (if id < 106 then (if id < 88 then (if id < 79 then (if id < 75 then (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))))) else (if id < 97 then (if id < 92 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))))) else (if id < 101 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))))))) else (if id < 124 then (if id < 115 then (if id < 110 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))))) else (if id < 133 then (if id < 128 then (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))) else (if id < 137 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))))))) else (if id < 213 then (if id < 177 then (if id < 159 then (if id < 150 then (if id < 146 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)))) else (if id < 154 then (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)))))) else (if id < 168 then (if id < 163 then (if id < 161 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 165 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 172 then (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))))) else (if id < 195 then (if id < 186 then (if id < 181 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))) else (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))))) else (if id < 190 then (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))))) else (if id < 204 then (if id < 199 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none))))) else (if id < 208 then (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)))))))) else (if id < 249 then (if id < 231 then (if id < 222 then (if id < 217 then (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))) else (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))))) else (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)))))) else (if id < 240 then (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none))))) else (if id < 244 then (if id < 242 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none))))))) else (if id < 267 then (if id < 258 then (if id < 253 then (if id < 251 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))) else (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none))))) else (if id < 262 then (if id < 260 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none))) else (if id < 264 then (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)))))) else (if id < 276 then (if id < 271 then (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))) else (if id < 273 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none))))) else (if id < 280 then (if id < 278 then (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none))) else (if id < 282 then (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 0, 2, 1]], proof := .tail 47 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2944)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 47 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2945)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 225 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2946)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 89 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2947)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 2, 1, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 265 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2948)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 1, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 149 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2949)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 2, 1, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 142 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2950)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 65 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2951)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 183 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2952)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 128 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2953)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2954)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 183 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2955)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 128 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2956)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 128 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2957)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 160 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2958)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 54 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2959)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 13 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2960)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 229 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2961)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 121 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2962)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 161 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2963)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 48 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2964)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 114 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2965)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 48 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2966)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 188 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2967)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 86 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2968)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 182 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2969)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 188 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2970)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 2, 1], ![3, 4, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 188 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2971)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 2, 1], ![3, 6, 4, 0, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 72 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2972)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 229 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2973)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 130 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2974)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![227, 118, 115, 186, 153, 7, 185, 69, 215, 151, 269, 248, 11, 213, 234, 150, 278, 27, 175, 228, 99, 205, 28, 20, 164, 104, 276, 165]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2975)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 245 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2976)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 34 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2977)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 226 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2978)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 34 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2979)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2980)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 135 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2981)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 1, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 34 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2982)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 6, 1, 2], ![3, 4, 0, 5, 1, 2]], proof := .tail 238 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2983)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 0, 1, 2], ![3, 4, 5, 0, 1, 2]], proof := .tail 2 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2984)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![168, 103, 115, 49, 173, 148, 98, 202, 215, 236, 82, 26, 11, 93, 155, 145, 221, 261, 144, 219, 275, 201, 266, 163, 110, 162, 260, 59]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2985)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .low (![141, 172, 23, 50, 173, 148, 98, 3, 273, 217, 82, 26, 124, 67, 24, 145, 221, 106, 16, 174, 174, 174, 35, 163, 61, 162, 260, 59]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2986)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .low (![42, 152, 107, 36, 78, 43, 206, 25, 92, 95, 256, 87, 71, 176, 53, 256, 87, 80, 282, 256, 87, 157, 134, 180, 154, 97, 22, 105]) }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2987)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .low (![42, 152, 107, 126, 74, 120, 44, 25, 92, 91, 146, 267, 11, 176, 53, 146, 267, 231, 282, 146, 267, 157, 116, 133, 252, 66, 100, 73]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2988)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 18 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2989)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 272 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2990)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![3, 0, 4, 5, 2, 1]], proof := .tail 178 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2991)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 6, 1, 2], ![3, 4, 0, 5, 2, 1]], proof := .tail 178 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2992)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 268 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2993)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 0, 1, 2], ![3, 4, 5, 0, 2, 1]], proof := .tail 178 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2994)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 268 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2995)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 18 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2996)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 272 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2997)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 136 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2998)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 211 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2999)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 226 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3000)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 2, 1, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 135 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3001)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![284, 68, 159, 279, 244, 156, 98, 4, 127, 264, 75, 119, 11, 230, 235, 210, 85, 261, 257, 230, 230, 230, 30, 184, 123, 138, 224, 283]) }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3002)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 47 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3003)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 190 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3004)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 170 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3005)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 158 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3006)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 190 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3007)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 170 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3008)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 170 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3009)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .low (![147, 21, 108, 254, 94, 247, 98, 140, 9, 193, 281, 119, 11, 6, 218, 109, 222, 261, 216, 277, 122, 249, 263, 101, 96, 131, 214, 283]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3010)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 242 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3011)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 170 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3012)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 170 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3013)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 166 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3014)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 212 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3015)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 76 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3016)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 177 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3017)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 62 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3018)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 199 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3019)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 220 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3020)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 199 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3021)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 60 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3022)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 199 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3023)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 199 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3024)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 60 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3025)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 60 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3026)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 45 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3027)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 220 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3028)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 60 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3029)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 60 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3030)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 2, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 259 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3031)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 2, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 137 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3032)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![56, 194, 31, 195, 237, 14, 191, 129, 15, 37, 187, 253, 208, 55, 38, 51, 253, 143, 1, 179, 258, 169, 197, 189, 250, 57, 51, 10]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3033)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 117 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3034)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 207 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3035)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 280 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3036)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .low (![132, 194, 31, 195, 196, 203, 102, 129, 15, 37, 274, 240, 83, 55, 63, 241, 84, 143, 1, 181, 270, 169, 167, 125, 250, 243, 271, 88]) }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3037)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .low (![46, 111, 223, 32, 200, 203, 102, 40, 39, 233, 12, 240, 83, 79, 64, 241, 84, 198, 255, 232, 8, 8, 112, 246, 246, 243, 271, 52]) }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3038)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 207 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3039)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 209 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3040)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 113 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3041)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 113 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3042)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 90 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3043)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 29 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3044)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 207 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3045)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 251 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3046)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 139 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3047)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 192 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3048)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 5 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3049)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 77 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3050)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 58 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3051)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 262 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3052)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 262 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3053)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 262 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3054)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 41 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3055)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 262 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3056)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 41 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3057)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 171 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3058)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 262 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3059)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 19 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3060)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 262 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3061)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 77 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3062)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 81 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3063)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 262 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3064)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 262 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3065)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 17 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3066)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 204 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3067)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 58 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3068)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 239 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3069)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 70 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3070)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 5, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 0, 6, 5, 2, 1], ![3, 0, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 33 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3071)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2944 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2944 ≤ id.val) (hhigh : id.val < 3072) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2944)) = true := by
  let j : Fin 128 := ⟨id.val - 2944, by omega⟩
  have hsum : 2944 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2944 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard023
