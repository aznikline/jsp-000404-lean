import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard022
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

-- Cycle fingerprint 00c4a225d149bd5b0884159ae197de1e629f37e609058772543980c25ba074bd.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0176baecaff74ea6807f2af8f291185f6256fcf15ccfaed8a7547b6210e28e69.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 01aa0fc07f64849656e2d848bac1e52c723fcd8c362163d56fd64bee4e6f3c24.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 02748c6e69455eb65ae7d2f2f1587aa4993b1b2dc6428278570396a0dbc34b1b.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 12 1]

-- Cycle fingerprint 03f23581dff888ea1e571439f06a535e6154c277060cb9f5c1c8c49b0b1fb072.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 0775d6d0e4afbd589ec92122a248f4cc0d90caa8e69131c7826437cc1be6ddcb.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 08c8181e14af3d5c89b0773d5db3bcc30544b2562ea2e8b601d78281ac7cb5d4.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 4 6]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 13 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 34 2]

-- Cycle fingerprint 0b41132e20b44dd78ba4220d3d9138d1ebcc935bbd2a4b2e98e907723e88c725.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 0ca00cdc1e381b5194ad0e7c80538aff3e5323d08d3dbd3362ca9b22f05e7586.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 2]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00011 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0ce6b13072fc70c3347eb58750d74ae0091be124f2c22c0d84202a3b38e9832a.
def localCycle00012 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 23 1, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 0e2f17e7ade78677f134cdfecedb57a1904c4f465b25576b38df2076e885a109.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0ef393964cd49a072133accba5e03b4b3a5ab12adb46f20b87cc1c5102feb36d.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 0fc9af577c74b4adafef651aa33236e51b6405cd65db222d9e2cef3c45937934.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 0ff3000a0139af5545b2fefb5a3d2ed3a8b4884d5475aaf3f9bf3732df45da2a.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, 0, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 10b5cf654ce4c73582c1a9bf67ea3f76df722999b33383a73caa6a402f31a7fa.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 14b0606c9962bcbfbff33faa28d1578d30f3733d4c212145afc4fc6640ad28da.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 14c083c6c9617ad0d7738896e55a58f0de4ef468a9e4d0256ec2f512e29ce8d9.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1501f0f137f93038a9fd3d64237a989a84ac36c023c8e9c773fd76232a165caf.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 151c5aa5921432660dfd56e7c7e387ab6cd14efee8232ff3c9f831110319db23.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 15c28a89db4d09daea2be7e61e945ea0327d05c21d2797ddd9905c12eab23a0d.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 178f579338aec374586bfc508b27ba4e3cbd40ed8772d70ff197559faf432fff.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, 0, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 17ebead4041e49966808c2828a9754b0fcbc31cb59f33fb40210a232be42d652.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint 1a236a503d4be24ce1c78d20d3eea8ab14780efb919167ef3ff5466af6419703.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 23 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1c8c5d5c007056d6695139dd87f6e85116542d338fa226c79f943340b3fbe923.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 1cf40529e58ecd348f08729f700ab863b5b1f2cf1f82ba82bd38b667934f0a3b.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1d2938958239ccdc44a2b9513f673f5f08934b578c4af0f138bf2ec252b17a83.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 1e25f01c0ef1202da1cde51e07a33074a799e35060aebc567682ac63007abc7d.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 1e5097d7f5232c6290a2083437aa870bf4d13d048f3441e1a380beaeb730215b.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 2180121c6b6f88dba1effd48f2cf15b74354d2ed44c4e2c7ba2bac51f37676ba.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2185d5e40e158f7a695759c957a9b473a4f9baa45138d5d72a5b184ae8162300.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00034 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 21d5ae36e49fdf50c149a61f8366764737d52f24d58cad992bd57a419cf15e7e.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 28 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 22404b30b56843c0c4dfac7cfae7a9bc13ffd9bcfcd80ca1bb12d9645ac74bc9.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 224bbdfd4fddd5eeefe9af3f6f7811226a52c0c95d8c26cba023571110034d62.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 249527f877c40f108672e8f97c230dda25ed3073acf0c6ae58e6e55dc3f1655a.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 6 0, .gapLower 0 1]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 276fee3267b4477f54aa680277f99efb8e3d0a126f0e805b42e8b238240b6a46.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 27ae1ce9ac871d962f62ec7eb8af9184169cb9a7ea002011d9ee71a046bb1c92.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 28db2d48469496830c523a3b9a3a2174dbd009e0dce30c8791bcee645ec4bd70.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2ac14ea54f163a412a8617cad16cdd770b0bc5db89cbfaee9643ab710eb991c9.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2, .gapLower 1 2, .triangle 16 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2b7c73f7548f1a1a902a93800a6bd8552e5e32142e64198b426646177da882dd.
def localCycle00044 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 18 2]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2bee6686e7520f570b60c7591f58ac9f652dfceda6e2946c7ad40975702fe1f0.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, 0, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 13 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint 2cb4747cb17f504d5cfef2733117a12bf9b5f0c4f46fde05b3d3fa394533ef45.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 2cb4de23f4f56609cb1c5390c5b0f8595067c55fbd68b4b75ca7c778d32b825e.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 33 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2d0e0c260e2c8d6540f2a5233d4aca4c5eb1ac3c0297251bbf286d48b95c75bb.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2e4b74e57176a45cc25b096070f15e763f4ccbe9f4179e2588d6031d72b6a4e4.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 4]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 2]

-- Cycle fingerprint 2e62e9f4e08e9610c4a79c8b32152e3367727572bb7398d7b4ba72a898a6ec04.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 328bc92aa871d295200366a398edc41bc4532405557115c38902adf8b8daabb5.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 2, .triangle 10 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 343d84678e9587e11aac4a67e5baa60e6451a3bc94227e2cd360dd6796070690.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -1, -1, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 352b21d0cf17f580c34b12eae4027b4fc8f06d90e9d366d9e1f937718819b9f9.
def localCycle00054 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 3600fbde3158584c6067c07ab1376dbfe2829ac2fa040d9f0a4325e1d7918ce7.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 3754687bb5fdc4a9fa8532989a0e914570cd5560c26689bbef74a7b71d01c729.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 382be7c2862699b4466a51eaf44f596802386b10da64da92ee94e3d73a812252.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 388957d4c411042708988882a744b795518d55b21b9fb79676387e8738ca2f1e.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 0, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 10 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2]

-- Cycle fingerprint 3975a7be970659d369510403ef8c675c11d5e120c18445b147f09100fe9c38f5.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 3dbe551122f8947322f827df98068866c44f1067cdba1c21cf383ef2ed742ac8.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint 3e28aaf952864c95b314c4518e0020d555de7e51041b7098911ae5ecf662ed11.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 3f35071fcff8f20a13a70171281920e220a3e3d2d7e44085e84915efae703c52.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 3fce33f0a4ef6d2ed42b85353910300024b71bce38fe09901120ece5ccf5628b.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 4242ae111ebcfae266b45dc965b281dd8b0c3b5525d368fc4cb4b8acbb68019d.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 4242f0c32e621a8022bf520efd336dcb0063ebfbecd3283f09a05db97c956177.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 42ceea46682113fd53c60aef3ccdd29c715d568cafa34cc5527d1548978c628c.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 44344627e4416af664b389d4409565361807bccaa9737a18c25e1b49bdb3af23.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 16 0]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 453428c574490bac0955ffcc45d562f518fcb7ae76df5a371af5e62ec49fcea7.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 4541948f7050a620b4c7fd32ba0a80b5826aed83e47b5a77cdd780a4ea6ea784.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 4566f68ab2ad1fd6adfb2c1a388f41f28cd41e265c846313c0fda6c68359f9bc.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 4827cc05af1f0ae1a24a2f33cbf9b72621c08880ab3a08033f9ee40a501cad08.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 486a7043f26d4c42b177d0ed633c7de1ad4929a09d24b550c1bb551e72663f42.
def localCycle00074 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 48cb26c1e574bdacc6618f9fbeef48cf9523825f9a45966c74e78bd252554d01.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 491c85482b92119c5e9b942d405ed14b6dc71f6151bb6cbde133e18108fac6ad.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 4a248c2a4a454c162d76fc61f84e8cc179f64790cfd2f613aeaf9b3962bdfcef.
def localCycle00077 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4a9ebcbbf930f9ba8f44551c4fb1f40b5dae5e5d3edf0545cb60b6f369b4080a.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 4b5dd22ad1b5c11f1669ccc483c98535c32d44ca4e183bd1ca6b50737df98e56.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4bfd73bd34a3b0152478a186d0253a4581222f363a6f5d85a945f6817e838d28.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint 4c3a4f8f1142b0282d9f13984be4a5807475b3d3a5d73376461b9d37f12b8c57.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint 4cdd7d2c2a664bb2e12fd93074b3d9ebfd6f2b1ecdc626317e4b1744d4262b95.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 4e0b07999bdfb8c8ec18410c3ce7dfff9a315239ba074ace947fbaac986a27e5.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4f4331e0e94fa3bfdff9a620ffc967e2f5081bce54dba537d04c86bf1bd6c7a4.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4f752aea4593c0666e28adc4c0620818bc9acad616e5d9b1fa659e66500728c0.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 4f82c5ec6e5edef96eebe505d6a6e3226e6519e53605c9d218b480070c6e8ff6.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 16 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 4ffd6e37edb57aa0eec9e961fe9241d68657d4fe083af9c9f5b128cfabb45033.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 50049a39a11dc73249b0d67c763ee42fbdd4a4059b5b4943143ea16e0550609d.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5045f08e7634c5aa7da3da9ec8bf40d75b930a199f04e0d3e569af5fbc07ab8d.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 50868a204e56eb51ce3b0d4f6c92cd2b5f5c49daefe7cf23fbe61293465ec561.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 51a840e6711260f4d07bb221acba27c68d815316b774b95ec8ee3bbb2517df2f.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 53025ec84d13af688cacc24536731a8140acd17911f12c724efecadaa8b79a1c.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 53b4ce8208e576e2f53eceb995e46f28e862ef7709c9fbf951914d0b66e57a8d.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 54ca3878f49c2bd843547607fa2cb44ba4a02d6a7a200b2f34d8fdb8385c02ca.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5665f0680b4c18da8e8e80fb05905da9c237343259a8371ef17c7db361a6e497.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0]

-- Cycle fingerprint 58444ba9fe53c69fc27e599b181545b183797f85282f9168a5b7b133128ce4ff.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00100 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5a29fa755a769b0e8f39d656ccdd4fa30833b041005dd1129dad0e5b00d594d5.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 5a6ae82bcd9a6ba5cc299f8445ba524fcf722cf2d07040bcb514d555486d70c9.
def localCycle00102 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 21 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00103 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5bc19d861d9beb29f5e07c2788d426e2b3b3c66dbbeb6b2bdc3eb1809921a254.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5ca08b61d4f3677c994735abef5a215f1f1b58891bd0ec147a6f218ecdc63ebb.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .gapLower 4 3, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 5dce886cc8f3166e2a784303c8fc3030f8cba966337d8391e71c439341e8de50.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 0]

-- Cycle fingerprint 5e52d4a29574d4be67238aa994a2d19aa218b52d823d0b396a16c6eb8243a1e8.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5ef8715d8ad860a65347baa69f2d44fbfa21cf76eefeec486638694418cf72b7.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00109 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 60c8fdf23d554a45536e53c976a6aed40ceb59900327bac9eb8837933d7da334.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 62662e8c73ef22352267ea9c2b8077f949983084da2a6be6c6873506622c58c6.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 62dc89605dd816ae2dd89fad39d3da79ca2237da9ceeb07fcdddc9f85ee109fb.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 631906d683496afc13b99515f13840dda49ae2a363fc2de6ae003ac3efd61b54.
def localCycle00114 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 63fad65c36bbbe445c6e17c8b1d6b01f64f647d7055aa75354ff50bdc1ca4f44.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 66321ea59e2d9bfc813b050a3df172210498fe8f208a534ec0e6ce5fbbb181d2.
def localCycle00116 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 678344fbb81adf88f69925e497cd4c5b3a2178995f5b3e462113c2aa3e82d628.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 680c2751dd2fe91a73b09949334e398a1671f14aa2fb33d069de1e363d106990.
def localCycle00118 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 6a1864bef040aee89c04787d7bb11d74c68e37fd3016cf98a071d9f28af07a1c.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 6b07e4a28729e5dbce620930295ff70bca59bc947a419f0f033bcbceb4e254c8.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 2, .triangle 12 0]

-- Cycle fingerprint 6c15d0c27904f9086aca58c892be32346d5dca3fabd57f77a90e3af0774b8bdb.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 6c76673ba5e64898338c8473825f0fda64156d7bc575097897ac9287e5915d8a.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 6cc10ff764e3e083eb8399071027cd5f36eb250ad085ea3e60bc489010d452cf.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 6d04c4ea559581ae30b8c363a1b8887db00a3ecea9969084565430a5b9599da1.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint 6da671d9086a82c813da16a4650b4a1c9d7f8700a6525e5e6c250831d58cbe60.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6de94747e780c4a48636a37c668dc0a84f2760918b43807a2d1ce91ce0176e77.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 6e278d69b185f8c03ee46394b6fa8bd2406420071842b7eb2939bfd4aff782f6.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 6e48d8f1454804aa890a50a4b5b5d86c4bbe56f65d97ddd9191fe2f9cc21ba80.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint 70634aabc32595c2344102e91ffa2d2dd40c68ec1eb2da9cd2e24f6985785294.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 71b39554e475198b351bef6b781d0aebeac743c029f6336f14d8f13d1e46080b.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0]

-- Cycle fingerprint 71d086f69ef9450f0b90f0676474a73763d2a8c2ba3290c69b60f00f688c64ab.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .gapLower 2 1]

-- Cycle fingerprint 724cc99720f09140141c7a211ccdbe1797edb46ad52b97712825b4bf386f758d.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![-1, 2, 0, -1, -1, -1, 3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 72bf50139abdc0bde6b88e3f3bc2ade37b94d31bc999337d9cff8d360894a91a.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 2 2]

-- Cycle fingerprint 730f59a4c900131a8b057876abc1e01aca64f9d986d0fe1e91eb08a6e8378bcc.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 732be887b54820cd414fe70975a0b4894ce975bc003cba0bb17ec170d9b8c155.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 73cd70b57653f5325171b6582759746c0ba9568e5b81a98f8a1e1a7125787a73.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00138 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 74127b2813beabab84baf8605bd7f7a75408970d89a67a07e613a9b0c37f1b33.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 74329b0aad173870305b2a16bba731aff7068408da1a41e0f00ecf71d70b43c3.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, true, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 786c56090b0f94fe60ab615e72b384e33270d08b16d0e582b752df215ae23c73.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint 789f30c8eceffb1c27910c921ec2f4525c9d33b3260d512d16f9312e3ab617ad.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 7abb8601372cbd27120d00109b76c25383976fe087ee09257fd962bd144dd5a0.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 7bda8b02f34cb11f29ad8a70a618844f5e8dbe725c5f99cf3bf57444f4b70102.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 7d2e41231421f840d9e4f10c140f13605ad72aaae54c16965ace81912fa4362a.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 7fed440a1fec8e3ab813c594ae8a58170010ac57ecf37b71f4636251f494fe1d.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8030155a32f6a919eeca98d59cfa75ef631ef344c0e5f7c1bcf9a3321320eff3.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 80888152f3b6be393c6fe20129525f4d754608fa6b24533692cde1d2ab61a50e.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 82c356938f38be75652a4625c1c373b80efafcacd6ea871422597613875e5ae4.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 83854759f02ad804944839b2a4200e19236023b2f5e7dafd713b44249ffd7751.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 83a1b812e8b59fb7b282eafdfa8a5f7fbeeeccf25a2597f00e5542056c84c252.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 83d3184bd2dff112cb402d98372e1b533ca9661d877963c4825ca62ae46823cd.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 84dbd38d61fc03413c7160d159f37e8710f21e5f47cdb1de76142dbd91d4d8cd.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 84fd6bb2c848943c5724004449f14672cbf369176e85732af758d4b81996d60e.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 85486d0474bd8c9160f8d62cd08dd5c5dfd02b62f661862560eb6f34d5a76f72.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 85e2fede2d4f310a29ac80cbbe1623691bf41df62cad7a0b8e8e67021b5cb630.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 86687ee51148f06cf2b189637bcc9b48aee9aa8299cff8456ea783e1980c9a8a.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 86c656e2369fe1b3bdf5ee2bcbdb72062ed470ddd9474487c53ede2725fce287.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 872c1a280eb29ef9b2df868b574b7b199cc316f084ec957a9468932728040479.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 87793ace0ac1767b909312dc017c1fd6c3ca2b2e9e4e498f904ecf3eba9d1753.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 877f4b8ec78ce3773d0e3c4f52d493c38a3218bde130d09bb8cfc68e945f3fa0.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8829fdecf88db7c5dc4c27fb1fe6776282d2bb0d1b46af7276c2b80a755d0036.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 887a48e65db2e281349c6b209cc4c6078692857d4a92ea80775004063c940a4c.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 88e21bcfbf8eb6b6a0696bf476aec8b575ea2f09c1d91fbff6116883e0084813.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00166 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8b81a1f8a5ac33de67657f2a3c9b2df6e61cc9b3ca5a2bf9a771587733baf0d2.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 8c2882cc933e2b580d8e3e5563f3c496d3b57d555240470319abc86193a41b43.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8e13b6ca5cba9287ce29f8026d0d047dcab81afd7bda81db0773eb74e638fb5c.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 8e80bd231aa02635e6f725a2148251121a266ea0a70a161a4644ea30d860cdcc.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 3 4]
    constant := ![-1, 3, -1, 0, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 31 1]

-- Cycle fingerprint 8e99ddb6947d25b9043012d5fee6a82e73cdf585c3063b30739900261bfdd335.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 8f101c5b2b62031d8563fa57c5670c2445ebe450fd2309cf3e744195a7d31327.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4]
    constant := ![-1, 3, -1, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1]

-- Cycle fingerprint 905024579f5ecd8f4fcf0512efcb015f21ebff0244b541fb719ca5ab7eec350b.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 9168961527df126c219b37eb540464e4c243a958cf00dae3df67d6c16f27b334.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 91743b375a88238dd36bef3626c795264c8966f4f93df05f8e1ffc1885836566.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 9259ed4773ae3d116c20fb2d2c1f1a5730735c17f625ae8e057ee9522306813f.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .distance 2 3]
    constant := ![0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3]

-- Cycle fingerprint 938a6f12187a2882106619c804f94b588c2df38500420540cef74b7d69d349bd.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 93afe1df27f763bd780b8b6c5580f2b6abb2fbfa9b3d08b162856047a924fccd.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9449d5624757fbb836dc121971b8c03c9b3cd8eb7ea5d54d6e439c489c0a44d3.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 954cc95f19f4f46604e3ed38a0ad32500c22794cf642518e085b4d266288ba11.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 959bf0461874ce1dada1d18b925af812bfaf314ce2805e06d2bb87117a1ccc55.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 5]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 10 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint 965a3c2621c3243a1cf524a4f7f8227a11c02d3073a768cc92a5bccc7f535700.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 96bfb704c29fa0db3dc577ba1adf329b4c655d589fe9e7be720e65afc4ba08d7.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 97954c9f1dde99bf6141eb265cb1af822aa93a2487ea9414b535ca47bcc9c3fc.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 97a27b38f45371da99c248c4d29d3e685b4d60bc4e9cc153c0d7d40563c6b8a7.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -1, 3, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 97a97a494518cf00afc68ab675d0ef61978b7a75bdfea85fbdef98baba6c2f09.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 99bb15ef2ecaaff7f11e0b452a2905c69964907899e6de06ad602041e152bcd5.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 9ab97debb8933da9eee8498c85e61b46c7fc1fc2632c5cc7dc8b6ded9377c73d.
def localCycle00192 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9adaa71c9cb9d5dccb8caf67a4a3d1038db92785769dd2ce6e0e6616de90f9c2.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 13 1]

-- Cycle fingerprint 9b68899fd6d83e1a8a3aa51a7cbf28c6f1e8fcab1f05cfaae04ab5d6aae87b59.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9bf606eb8e462753d30ccd5d45ba1c59fc6692695a892c239fc5013d17fe6bf5.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![0, -2, 0, 0, 3, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 28 1, .triangle 6 0]

-- Cycle fingerprint 9c9cf7b56012bf0f338aeb954602ff5e2aa5024a62d6cd178a5a02cc5b1e0f78.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9caafcd04e2e6f0ce9018c66d3bf1d6d1e1c74ade600a1022aa2d330893a56d0.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9cf73b6b1ff487ef9b6c1756b14f1f3863bfcf8463087fc6bddaaf2bc7f44162.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9df9768de6ae9cbc5d869c68b104852abc2e0320b8dc35c89960cf08f2b26668.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 9f763a901518418d7c72d035d5cfbe30b8482cb2146451fae1b071279f8c85ba.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a18d3e52b9966216309e19a014a486343d9b119fb7e04b1843d18436f094da2d.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint a5ebfd2850fc1da1a6c059ac537fcdfd6724b3aaccb3e362571d91c80a3f7802.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint a774a57eae688c8a66c2c167e1b33ad56088c5b3e6b4805e9d51bf24475334cb.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint a7927311efcd0e95fa826ba09d48ec0c7ff06f2d497d31cc224ce55002931d87.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint a8780ad01977910a805f97d14e69130909c0f03b6cfb8e6d0c76a89086fe084f.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint a94fb6acba0147a89228244fbd328471516b149afb82d6b04e8ad54953a180b5.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint a973d1ce0891db1eb992ecd717d0dea7cad8a2bb6a3fc4678aa09f2bb1afe715.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint aa116368678123ad409d0e489b9c10d95ca685ed05e0acf8df5cd819e64a0fb0.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00209 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aa67f5357d7e8e9fb270cada6cf649bbe4e7b01edd4cdc8448f47614b7da2c3e.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ab18c40d4cb6e2eaaaca33ecd6603fa6da4386d36ec65f465d4ec3ca945e2d37.
def localCycle00211 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint acb3ea0e3ad98c068db0531f06facc6adaad0557254fbd487cb31e5d502501db.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 13 1, .triangle 32 0]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00215 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ad72924072111d9f95e673edcdc05dcae8b34e6f7cbb9db50f34d92729cd50f8.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint ae03400d038ce89283af157eb40fa04ebc752c87cebd83d249b2355ed2a06c1c.
def localCycle00217 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint ae334c39051365a3c58196eb8b411d4a9006798ec1ec6a577dc01a7e904f48c5.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint ae7a9d2fff67437f865e58c733e9592f1f1f3b8edc77f9d1568f3dccd9562dc4.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b04f30e924796800b762ca0f6ef99f8445917e0b8da037e22c23345cc52cdc3b.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint b246538a576683c071ac5fa1166258d394913894e49cc06674eecd2d45c3e610.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .gapLower 2 1]

-- Cycle fingerprint b296906f5e4273d2835b3d50f5c47a35782bfdd1b7c0ace9f8a0de6c1684a1da.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b38f819ac6e8037d268f21d97ea79112e3de0576ac967d3a8d29501408ea6c07.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint b464592f2c9f6688abde1e561f15edac777317bcd9f37e3dbcc6f457e615a1a9.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint b57257c749df6f95d8bf332f60b6429d4fee91fd801e0d222685b5b8b78242a0.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b587b10f00164c237b794e08ef405e6642ca6a7ba829c6f81c4b94db1e32cbfb.
def localCycle00226 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 2, .triangle 10 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00227 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b5b8340cb3b8b1d5fd803c5962298a10ec2e4b0b1fcf2f4c9afafada6d06a57f.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Cycle fingerprint b6603c48ac9eac8a755620596a04c29fb1b853b4a3d145082f43d3064414f811.
def localCycle00229 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint b7d282b64a072da4b70cd21ed173fe2619736547671aa0edb1b77ef4e24f106d.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint b8a2afb31e3d5bdd2c81362f2ae718cfc844e285f3418ae430485f27de9490ea.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint bbda9a6aed76a4956d87de271c71c05d20c5df3d4652c02b01e6660fd0cd1cd3.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint bc4ce61628607b953dc3fc7671d80050093d89607d0809d6d4121c37a7d1a8af.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint bcb841f2910e19fbfcd47cfd188a37a53ea3b3b5b60b4957e9d96b22ff7bab72.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint bd59dbf5af3548c7ddc92b50f9e73b12d04342cf4846ecd074cd02469a9a92ce.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint c01afb07aa35b287026f5a3945cf6a1f785165c4886127aff655c2900dc5efdb.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint c0d2757201d2fefef7bfe4e00912135158fe9bc0d8c296e673b73de6dc13fece.
def localCycle00237 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint c205b1c7678706edd3b8a7f70f883c4234b5d3a0cd22a231355d22293023726a.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint c38a1d6466e58dcc1dcee93b5ef3eda3646daeb180c124e49f356bcfc4bc6941.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint c4662fa93e8391664655c7adda327bdb7aa555b5c14d16d571143b8aebf76133.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .gapLower 4 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint c4db3e0430c3bd7ecd52bcc5d0610f0aa21ac0930f8febc36a8ea47c42c6bdc6.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint c5a478f2cb02060f82e994e8683bb9547ec684f0a249d0be7c4dbabea6d5435e.
def localCycle00242 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00243 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c79732f4317e7bf2504e441f1234944da57fb63a4c3e243f5a339a75616c0945.
def localCycle00244 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 6 5]

-- Cycle fingerprint c82d056eda0720f32cf7fcb93b85c6cf5fab6d0d9ad33920eca8b6e699834269.
def localCycle00245 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c92291c805e47eb266126a768eeec92b633e2775103f1a4de980543141a8cdc3.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0]

-- Cycle fingerprint c97d421e6c87b89dc0b81512cff9338f83b4e1f0d5077ab174cb5ec6aca1e013.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint c9a97a7bb417d47fcac397b205e4f87b7c14e21c99dc50e0216b5a8413671dd3.
def localCycle00248 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true] }
  origin := ![.triangle 16 0, .triangle 6 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint c9ddc208af3c5cfaa34c1b57aed353545b3e3d2a54e95c433406963aa93dc07f.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint ca4885f03d6afe438926a7393ac939d90de0891b092f7108872cf14002950f84.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint caf42417d449d58befc1b14a8dff623b59bfe86e1d52dbef817b1cbf2c7cfe6d.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint cb4a20e41896ac38bc7530538c88fd912d3474b17aaff2acb238ca68b2be72f5.
def localCycle00252 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cb80f22d5191d71bd577c823061900a9717f2a7580863e4009f34b18df29bb3c.
def localCycle00253 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0]

-- Cycle fingerprint cbd453b2cf674fe0802a4de8308d70488a53c0cde517fcdc5e31cada6ca3dcd1.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cd4a8c54c7da74d8985fdcf56e7f9f70396c7b3ae929818c84f02f784a6ec12d.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint cfa727e5947f852e0d436752b2f1d413a60c166255cd06ec0e5798e2b461c8e2.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d1b19de2d2bf6ac58468aee1b4242853d32aa7ad7bccdd55e11d33a6278ccd57.
def localCycle00257 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0]

-- Cycle fingerprint d1c4b01732f7ba71383d0c47619e73e98794cb6410fa019b6770622046c00d32.
def localCycle00258 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d1d05e844354705e850575f7e40df910ef04b7dfeb6c58b7f4285ee4c4040d23.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00260 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d297af23b9c31b53664708f32449de11f2f2a8de2666d2f5963d2925eb95844e.
def localCycle00261 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d2ae7ba9b32715403d765aababc6bec6067e41e71c3b87a240d4ba577ad29f04.
def localCycle00262 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 4, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d2bbdf37239167176b9793735551687b887063d0e03d122655f51e1772e2f532.
def localCycle00263 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint d397d0c766bae960d3d34a48b9d7c85aca0fa67026073edf0b8a57a926019080.
def localCycle00264 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 0 0]

-- Cycle fingerprint d458713f2476c9bc16bcaaecaebfe1294ac2dfdb972d5822d807d8c25c067ad1.
def localCycle00265 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d4d9727772551381b138fe0483b14b7b3d72af96192bb07cebc4ed24e742d97f.
def localCycle00266 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint d60190818687af9f24a4479252d78ec4f1e13d5f4dd1d5aa9f2d7a90e123b3cf.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint d76e6c190bf37d02bc1fab8a67a9644be952f7c59c16f234e4bda5d82efad538.
def localCycle00268 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 6 0, .triangle 0 1]

-- Cycle fingerprint d933ad946142ad3fec6f0ebdb797894053bd7e4acd9b4ed6064fcc2f94f2f668.
def localCycle00269 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint da41de3f4b8bed1aa6c1576dabdf0b665455f4607aae17e5ece1ff7a4fa1cd90.
def localCycle00270 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 2, 0, -1, -1, -1, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 2 4, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint dc21b5a65f3233f74bb487abc3a1d0988134dc049227311a7a464bf7f5119d56.
def localCycle00271 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint dc980dfc27f0a7a0a57f97cdcd5c5572745ae81c4f2baec2235d8bde442d366c.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 11 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint dd05066571d17efc2588a65c19a35213fd1b443cff964507b9bc2275707419e4.
def localCycle00273 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint ddedd9bf2d0babf7a115868b1cb0d51def2ed16005f3da434b16bd15d295f851.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e051a3c53b4ff895a6173b10e0b25b98bad77117e242c77c350151f88f5c6b03.
def localCycle00275 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e068f7b9c206da40b80230e1a677c35a878f58e90c674bae924c20a6d691cbc2.
def localCycle00276 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e22763b22e15d15084ab0d1cd4b585974ca137c2e78d0a0deeea7f47f294da2a.
def localCycle00277 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e28abb363be99d95147e9fdfb77e05fb9daf7123928df4db50e84b74f5c4809f.
def localCycle00278 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint e34c804396f7e0d246c05e12a10e48463a4382f54aa86cad81cefe87b9697357.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4]
    constant := ![0, 4, -1, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 4 0, .gapLower 4 6, .triangle 29 0, .triangle 16 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0]

-- Cycle fingerprint e378caf99bf5b6e3cd79c7d782c1ce5084029ede08ab209b619d58c9015b8ea8.
def localCycle00280 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![2, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint e3aea787839f5eab33d6ce6eb34f6b3c190893faef27be89c5d73ba8212e4618.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00282 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e5cad8ea41a48828c93a7823b2276b3f135d37434e759ee2418157da6b24d8bc.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e67ff67737e6a6b090d0220f4e257373557da3a167542551597cd59a5c9f23bc.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint e74c1eab802b66ed7ffac390e03fef04b8bd18bec9abd03671cbd04844c78006.
def localCycle00285 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint e7950f6f8536c1c14ddbb925e5be7216b557ba4106531f621b8f98ae13341af7.
def localCycle00286 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e83cfddab0ec1be74cf75d48fefdde28a20889286c9ec3d23eb56d9ac7083529.
def localCycle00287 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e841e3efb2ae5eb1b8ee122ef6b051ffc4afbc2be739fef15a6d8fc8e2c67913.
def localCycle00288 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint e96bed7567741e195a3eb8a794e0b10568d3ad79e720908c19ff8ad803495fd9.
def localCycle00289 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 5, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint ea2624f442a032328282939bbebbc091bbbed21f015180765ae2c1e2ab9667b4.
def localCycle00290 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 5, .distance 5 6, .theta 5]
    constant := ![0, 3, 0, -2, 0, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaNext 4, .corridorUpper 2 4, .triangle 16 2, .gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 31 2, .triangle 33 0, .corridorLower 5 6]

-- Cycle fingerprint eac40286db67525356d052a6c8de2ad24c6edb740d52c9b3b683c466ce253f2b.
def localCycle00291 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint eaf55b498e55c314791361eef4e4bb8276742e197d39314c5234b692635e3977.
def localCycle00292 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint eb4caa3bd63024c2eb7346221f3725d65963053c544d18a277731ca05934afb5.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint eb7391bdcd1fc4ad01c46036c14f3eef27bdbf53ca7a15db5a372e46cba5f4b5.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint ed917f470287c01f30ba155c01e06dba057904e982a3d80eb66d70902a067777.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 2 4, .triangle 16 2, .gapLower 1 4, .triangle 3 2]

-- Cycle fingerprint edbe47c92e8318715c1c1359ab0477423e4a27651a9faf442d0b87ef10f58b2e.
def localCycle00296 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 32 0]

-- Cycle fingerprint ee60904ce98f13225cd0123a8d985163fa879d46878086915e4bbf151817eca8.
def localCycle00297 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 4, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 12 1, .triangle 31 0, .gapLower 4 0, .corridorUpper 2 4, .triangle 16 2]

-- Cycle fingerprint ee9a56fb3dec47a1a354884ed110d62ed5de23b340f7ffa5d2635d645957cc38.
def localCycle00298 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f0e2211c7b2b2f7515b11651d9177d399fccd3b1bba3a1349b38cff3a0dbdf70.
def localCycle00299 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 11 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00300 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f1730cfe4cc2ed8d00097898db41ecbdebcf97e7719d043fb6ad3882be853c55.
def localCycle00301 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint f2b783cd873dd472f64b6ae83474b525fd2d76dcde37f8e5569ddd031eb78e52.
def localCycle00302 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint f309dd6c6c266fb055c208b2f5d0d23bf3c3aa313dd07ae7d5ef4bbd4f7b2129.
def localCycle00303 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint f3a4b16ee080da2ded88f23739c4f9e67227228cb21aeb98772628b58ebf50ab.
def localCycle00304 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f40b7fb733b878138da46ff2dcad1188112d2f9fdfe7162a963f2686b10550ad.
def localCycle00305 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f4c18c9e11faa4e74735d71e9b2e51092bc28ab36c6140edb3892c5646d20878.
def localCycle00306 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f4d4f2bd49a24d1675d8a762bdb8d132d16550bc5dd8a84dc9d70cff0ec01a31.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint f6da4664ee310d76b245729828857409e8103026ecfac1b219e002e0b6c20e64.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint f7a2423bac1716e4f25c009a98cc2a8df627a4236b267f697ec6e4df7eccb848.
def localCycle00309 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint f865562efad7d922ac5a9569825d6b9ea0db14ae02914cb0fb410bb4024a7520.
def localCycle00310 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00311 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f94d7d4475d15867b498e342e2f9478b7f082a307b6088df3802abad7eaebdac.
def localCycle00312 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint f9f71deedb7fc2b2e1edf720b7a74bcf03ee955dcb87cc79ce83de8a8e0bc6b9.
def localCycle00313 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 9 2, .triangle 12 0]

-- Cycle fingerprint fa741fcedd11c34c00f0986e0e6c70b98d28c71a1bd748e2495df35dc186a51a.
def localCycle00314 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fbf8bdc85b80422860927dcf852792628bfc83d8a53b93beda2169efd771e26d.
def localCycle00316 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fcab0b37e5a31e453f05a695b900baba2660f4985283ab780b86f99dda04d57f.
def localCycle00317 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fd99f7e7e17e150d60be77493afff7867319fce0fa5115b1c810bb77f9381920.
def localCycle00318 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint fead76765536621f4e9834afe424bb4c2dd29a9cd7b3f6bfb8b745bd6ef97103.
def localCycle00319 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint fef5c9e8d1adad2d29c8b4065e9b3a5cf1384fc8f8da6da77044058e743ba8a3.
def localCycle00320 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint ff273d2abe6387c4dae86eff71d119012de850faa64aae5c2f215d11447a741b.
def localCycle00321 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, -1, 3, 0, 0, 0, -3, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 2, .triangle 12 1]

def library : Library := fun id => if id < 161 then (if id < 80 then (if id < 40 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))))))) else (if id < 60 then (if id < 50 then (if id < 45 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))) else (if id < 55 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))))) else (if id < 70 then (if id < 65 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))))) else (if id < 75 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))))))) else (if id < 120 then (if id < 100 then (if id < 90 then (if id < 85 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 95 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))))) else (if id < 110 then (if id < 105 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))))) else (if id < 115 then (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))))) else (if id < 140 then (if id < 130 then (if id < 125 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 135 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))))) else (if id < 150 then (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))) else (if id < 155 then (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))) else (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))))))))) else (if id < 241 then (if id < 201 then (if id < 181 then (if id < 171 then (if id < 166 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))) else (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))) else (if id < 176 then (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))))) else (if id < 191 then (if id < 186 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none)))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))) else (if id < 196 then (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))))))) else (if id < 221 then (if id < 211 then (if id < 206 then (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))) else (if id < 216 then (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)))))) else (if id < 231 then (if id < 226 then (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))) else (if id < 236 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)))) else (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))))))) else (if id < 281 then (if id < 261 then (if id < 251 then (if id < 246 then (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))))) else (if id < 256 then (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)))))) else (if id < 271 then (if id < 266 then (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)))) else (if id < 268 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))))) else (if id < 276 then (if id < 273 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)) else (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none)))) else (if id < 278 then (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none))))))) else (if id < 301 then (if id < 291 then (if id < 286 then (if id < 283 then (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none)))) else (if id < 288 then (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none))))) else (if id < 296 then (if id < 293 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)))) else (if id < 298 then (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)))))) else (if id < 311 then (if id < 306 then (if id < 303 then (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none)) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)))) else (if id < 308 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id = 307 then some localCycle00307 else none)) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))))) else (if id < 316 then (if id < 313 then (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none)) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))) else (if id < 319 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id = 321 then some localCycle00321 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 1, 2], ![3, 0, 5, 4, 2, 1]], proof := .tail 42 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2816)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 2, 6], ![3, 0, 4, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 82 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2817)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 1, 6, 2], ![3, 0, 4, 2, 1, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 294 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2818)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 1, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 147 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2819)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2820)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 198 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2821)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 1, 2], ![3, 0, 4, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 135 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2822)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 0, 6, 4, 2, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 172 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2823)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 261 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2824)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 9 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2825)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 160 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2826)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .low (![88, 143, 227, 320, 209, 27, 257, 56, 112, 264, 38, 276, 11, 114, 203, 317, 276, 24, 86, 114, 114, 114, 202, 83, 271, 62, 152, 124]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2827)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 267 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2828)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 174 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2829)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 4, 2, 1]], proof := .tail 215 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2830)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![221, 212, 34, 229, 189, 184, 159, 136, 316, 312, 142, 195, 11, 254, 121, 185, 76, 149, 37, 43, 281, 50, 5, 107, 183, 127, 102, 49]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2831)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 108 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2832)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 278 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2833)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 252 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2834)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .low (![35, 212, 34, 171, 109, 289, 186, 136, 123, 210, 134, 54, 11, 170, 232, 162, 54, 149, 99, 205, 177, 23, 218, 18, 69, 78, 272, 21]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2835)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .low (![35, 110, 243, 103, 109, 289, 186, 72, 39, 210, 134, 54, 11, 68, 232, 162, 54, 214, 173, 205, 7, 7, 218, 18, 69, 78, 272, 21]) }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2836)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .tail 52 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2837)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 61 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2838)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 240 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2839)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 61 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2840)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 4, 2, 1]], proof := .tail 93 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2841)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 70 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2842)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 125 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2843)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 273 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2844)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 163 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2845)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 79 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2846)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 196 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2847)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 208 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2848)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 2, 4, 1]], proof := .tail 231 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2849)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 80 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2850)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 57 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2851)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 196 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2852)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 201 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2853)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 2, 1], ![3, 0, 6, 4, 2, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 63 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2854)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low (![194, 176, 95, 307, 251, 285, 1, 75, 36, 192, 291, 6, 11, 164, 180, 277, 6, 249, 65, 191, 6, 150, 115, 6, 288, 122, 16, 265]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2855)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 4, 2]], proof := .tail 274 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2856)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 1, 4, 2]], proof := .tail 151 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2857)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low (![88, 143, 227, 320, 251, 285, 1, 56, 112, 264, 268, 6, 11, 114, 203, 317, 6, 179, 86, 114, 114, 114, 202, 83, 271, 122, 16, 265]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2858)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 4, 1, 2]], proof := .tail 311 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2859)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 300 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2860)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 0, 4, 1, 2]], proof := .tail 126 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2861)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 267 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2862)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 4, 2, 1]], proof := .tail 228 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2863)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 0, 4, 2, 1]], proof := .tail 300 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2864)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 174 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2865)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 4, 2, 1]], proof := .tail 215 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2866)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 0, 4, 2, 1]], proof := .tail 42 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2867)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 61 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2868)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 61 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2869)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 4, 2, 1]], proof := .tail 93 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2870)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![3, 6, 0, 4, 2, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 172 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2871)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 2, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 2, 4, 1]], proof := .tail 231 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2872)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 80 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2873)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 0, 6, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 63 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2874)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 2, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![194, 176, 95, 307, 250, 178, 318, 75, 36, 192, 291, 144, 53, 164, 180, 277, 235, 249, 65, 191, 156, 132, 115, 31, 288, 145, 12, 58]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2875)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 274 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2876)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 1, 6, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .low (![302, 225, 303, 217, 130, 178, 318, 292, 204, 262, 90, 144, 270, 263, 25, 238, 235, 223, 44, 207, 244, 244, 310, 31, 2, 145, 116, 58]) }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2877)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![88, 143, 227, 320, 230, 71, 318, 56, 112, 264, 268, 248, 11, 114, 203, 317, 200, 51, 86, 114, 114, 114, 202, 83, 271, 67, 283, 58]) }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2878)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 311 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2879)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 300 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2880)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 0, 4, 1, 2]], proof := .low (![40, 166, 100, 148, 260, 92, 20, 26, 89, 87, 41, 106, 8, 190, 45, 304, 106, 33, 315, 10, 106, 169, 296, 314, 32, 139, 295, 280]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2881)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 1, 4]], proof := .low (![131, 309, 138, 282, 84, 128, 318, 301, 28, 211, 161, 15, 11, 146, 104, 168, 129, 51, 101, 96, 85, 133, 306, 259, 299, 269, 74, 77]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2882)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 117 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2883)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 0, 4, 2, 1]], proof := .tail 300 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2884)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 284 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2885)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 215 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2886)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 0, 4, 2, 1]], proof := .tail 42 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2887)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 226 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2888)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 240 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2889)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 93 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2890)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 3, 0, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 48 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2891)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 2, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 298 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2892)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 80 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2893)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 0, 6, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 252 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2894)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 0, 1, 2]], proof := .tail 311 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2895)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 287 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2896)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 247 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2897)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 0, 2, 1]], proof := .tail 228 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2898)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![3, 6, 0, 1, 4, 2], ![3, 5, 4, 0, 2, 1]], proof := .tail 287 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2899)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 1, 2], ![3, 5, 4, 0, 2, 1]], proof := .tail 247 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2900)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![3, 6, 0, 4, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 219 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2901)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 2, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 0, 2, 1]], proof := .tail 215 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2902)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 4, 0, 2, 1]], proof := .tail 93 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2903)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 80 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2904)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 0, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 105 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2905)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 311 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2906)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 287 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2907)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .tail 247 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2908)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 117 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2909)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 287 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2910)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 3, 4, 0, 2, 1]], proof := .tail 247 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2911)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 1, 2], ![6, 3, 0, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 219 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2912)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 2, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 215 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2913)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 93 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2914)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 80 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2915)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 105 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2916)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 311 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2917)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 175 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2918)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 64 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2919)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 66 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2920)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 1, 5, 2], ![6, 3, 0, 1, 4, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 175 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2921)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 64 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2922)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 1, 2], ![6, 3, 0, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 14 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2923)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 2, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 319 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2924)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 155 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2925)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 308 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2926)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 141 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2927)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![246, 119, 118, 279, 253, 30, 19, 60, 236, 165, 199, 113, 11, 233, 258, 199, 113, 29, 188, 199, 97, 224, 305, 216, 242, 120, 137, 275]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2928)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 55 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2929)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 1, 6, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 157 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2930)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 158 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2931)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 157 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2932)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 0, 4, 5, 1, 2]], proof := .tail 239 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2933)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .low (![181, 98, 118, 321, 213, 22, 256, 222, 236, 266, 73, 187, 11, 91, 167, 154, 187, 13, 153, 241, 187, 220, 59, 237, 182, 193, 197, 234]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2934)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 1, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 157 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2935)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 4, 0, 5, 1, 2]], proof := .tail 239 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2936)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 0, 1, 2]], proof := .tail 3 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2937)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![3, 6, 4, 0, 1, 2], ![3, 5, 4, 0, 1, 2]], proof := .tail 255 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2938)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 3, 4, 0, 1, 2]], proof := .low (![40, 166, 100, 46, 297, 286, 81, 26, 89, 87, 206, 293, 11, 190, 45, 304, 293, 313, 315, 10, 293, 169, 17, 111, 140, 4, 290, 47]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2939)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 0, 1, 2], ![6, 3, 4, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 245 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2940)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 0, 6, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 0, 4, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2941)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 0, 6, 1, 2], ![3, 4, 0, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2942)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 0, 1, 2], ![3, 4, 6, 0, 1, 2], ![3, 4, 5, 0, 2, 1]], proof := .tail 94 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2943)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2816 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2816 ≤ id.val) (hhigh : id.val < 2944) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2816)) = true := by
  let j : Fin 128 := ⟨id.val - 2816, by omega⟩
  have hsum : 2816 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2816 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard022
