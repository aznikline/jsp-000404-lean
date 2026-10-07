import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard098
open N4R2OuterLeftReplay

-- Cycle fingerprint 000f032e595c68217f95ccae330495fd0b41d33242cb97014fa4909ecfffb68d.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 04e48b1159ee5accedab0d1f1d0ff521dd679b002263405f76eee831cfd0655f.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 08a43d5fd94ced296ba50d43c1cb3b51e062dc15d8d5c0d7808a46f5bc3f1583.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 0becec685beaa9028b1e0929c48b022454176fa28d4c9facacc51ce2c6cc1074.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 0d7219b30dbd7504e9825a7b4f6c360b264f29e729b8bc426a0653cdc3570794.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0e1887ccc9ca0d0a48beb47926fc485aab56d7a71306eb175e02f79beea378a1.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 10f273767b928372c88465636efc0e333650d393e15069d40e6481b116154bee.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 12cbb05348165d9680113ae4acad750f48826aac102bc3755d0aa47d7e591bf2.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 13c4d2ae1c664cfe0907066fe91f1773424cea014220e700e0b11ebed926aca9.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 144c6a2052725c2303b2af123cbdc17e12e91b79d86cbffc6111d6d35639e995.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1589f49d9c5af7c08ab3961bee3480a833560ad1fa0bfdf7f6746a6f1e44a822.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 194409b18a3988769bca2d20b0839c42973408f0408d992e03432a2aef3c7cbf.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 1e17f00cccdb6e0662f49cf0f11613a445dcf05035a2ee866ec12b41d13589ff.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 1ef7ec56d46fd0ac53344b7d55e8470adaa931561ac1f38bd2f949e10a799b23.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f43d63b44ac12a406b948ef33b8cab402f0e00c3114fd72b5c632b43e1f21ad.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1fa25d3c9b392cce1f75fe682bdac77dadc35743fa5247be8ee6bcdc40a42d1c.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 1fe581e2560997d7c9d98dddc0124321fc85964d4f1d17ae7f27343e231db964.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 212707d1c4897ac7eb4fb713c4a1625a763075dae5002419feb11f9d46539bdb.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 2407806591568437839df100b0499c08e2183deff2d9e19dd14770bd0fd84a5d.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 0 2]
    constant := ![2, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 0 2]

-- Cycle fingerprint 249bf6c009ec73f838c9f517fd82bc48d51eabf6e6bb95037ef0eb45ee5e6592.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 23 2]

-- Cycle fingerprint 25f1ecd90732b9940264094f64ac077b2bc834b1b68f7a799ce2684dfe8a58bb.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 267905812701e4ab35b108629c5eba03827ee7b34c4da61c39bd348239a0353a.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 27e10d64d3eeb0dd531ba03f82587103561e8fc8f2145085f0d16e672c098cd8.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 2, 0, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapUpper 2 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint 2801494d249c88e3ed69d181a752a91eb44a0c57652f0575102354027d88dd6a.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 28178ec1283f581ff01b9b519a0f763cf7f4247a02b8d1d6ebd5e1bdf934b07f.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 30f9b0600ae3deb94830bef74196c16f4d734db15f2b97102a63b9fcc53be5bb.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3145bac4a4da9f06c39c281872cf2ec95aa8896bc9cf97b68579d0f05e39cd62.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00028 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 32479988cea97db2284b7750d5787ebe19fc3c350b759a3d2d1de73c4577f67f.
def localCycle00029 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 332cc52b7029845fffd531f30bd5044cef76231465d7003a6fea911e467a4710.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 34b3e6af434e0203ce81e21f43767064f82d6c28b71e016856cd4cbab4ff5b99.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3]
    constant := ![-1, -1, -1, 4, -1, -1, -1, -1, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0]

-- Cycle fingerprint 3a5e70fb5017b3f27454bea47e1f7013bf954d84046ab535007216a07eb3f128.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3b6fa0e0d64dcc88d2bb5793c03a71b2ccf1ae5af43870e8b13153a8bee2b517.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, 0, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 2, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 3c4647353407813c2ae47bea9f4ed63f4bb712671ac0446eafbe8061cb5b5458.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3d7ce9e0f6ec5c151985563855f1fde47652348fdb9ac38ed2b174a19f42b895.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 3e92951fd5d046e8d4445a57e961029a19b14db0faf6f2985f6d3a982e7cad2c.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -3, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 3f0de987ee7ec2a7df53413973586ca15e21179d12b65b74f85c16cb454f600f.
def localCycle00037 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Cycle fingerprint 3f7c8b541e2cc05a445243ecbf0b7d4c2de2c3d48db6eae3ac08c04897cf1326.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3fbcaba58579b28f4d2375d9ba765eb3b9af6ff38a57af94035f9785012822e3.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 43294bf66853e9c401059e782084861dbe16a9092fbc08b0c521707dcbfa567b.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 13 0, .gapLower 0 4, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint 43ea03350251aa6ed34fe0aadba2df70daeb06de652353eb4b222563a45fef78.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 44cbc95e7ee54ad182f0ae325f6b4a05b551a7e2ceabd9f4a95691f45f19feba.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint 494a82f105d0dff122e15408f1eb046b410d834fcc7e61d632488ebaa69e7b0f.
def localCycle00043 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .gapLower 2 0]

-- Cycle fingerprint 49b7cfd875c92a414d4d9d24f0165ad297a7bf38a1e0f26e1e9d6a472ab41337.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 50727fa54f2557659886a5c31c88f5ca8430abc9f8205b69cd918182a551f8c0.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 50b2ba7908da3c34a4175a4ec0656ca29b1d87ef070fdfc8c21d3f41d75652cf.
def localCycle00046 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 5 4]

-- Cycle fingerprint 558df0ea3f68a3e7515b4bcc52e6155137828a033d3f8765f93c1425ea6886bb.
def localCycle00047 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 5620c003cd5ca6873a37fba58f8b7e96a43934da6e2df479f0bcc3631a52d29f.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 57761b2dffe9f7108500e0dade27e5558e29dff9838508279a86847a2fc5df4c.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 59a239b3a6e0ad966af105ba49a252b48a7458b9c4122b9cc7ca83045a45cc29.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 59c6b5444b19820c8ae21a50549af1c9f0f0c2f9f8a7b3c4f5c1b5125092c1bb.
def localCycle00051 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 5ad29b072c2d8d8d931b349f16bdbe75c71b18519c9cef68d3bac1e8f688fd6a.
def localCycle00052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5d189e97bb803d21fbc934c1896da3820fe94a622d4d5127186f0bddcc819dd7.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 5d2e73881fb2a468aee375b14d2c5bad7f352338b3e6495ee5699bfb84cc89a6.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 5f9b41e43f4521d9cca4998f203a27ae6257743361cc5fdef3cd4eac6847c260.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5fdc16a3e47a9153c028f74024eefd1e608e01f1942f46bd93d01cfe20848055.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 64d5a9431b08944c0855d7cb6d0422502e273223dd010b78330cd07221ef981d.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 3, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 694fdb9ca17c0d0b2ad6a889fd68ca17c63bdc70713595d169007c171d19b119.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -3, 0, 0, 3, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .triangle 3 0]

-- Cycle fingerprint 73f028b8165c84340ef330b85e66187ec19edfd7340563a62df9b3951c0b8fb5.
def localCycle00060 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 763e3978f735da511fbd62f7246ab3e382aa6895795fab6b1acdfc0fc9254bf1.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 7bc5d5416497821f8f25342cb1f9c1de321369af3fa5c525704f59514861794c.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -3, -1, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 7e540ecc16f8630aa844f2b69334d668f0e9fef657ee13e1051b5f2e30fe5115.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -3, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 7f263cdeea34b520725d37b40e01046c9a241b9818a476731d938d912d3c5b1d.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 7ff419d4f88d4c408da8c94e84138cdefe1aeb7ce00582df83623d31c928a5c8.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 80db139be156f0a049c2e9ef01bd642fd07b936ce397723c4657c52fb41aa03f.
def localCycle00066 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 817f59f779017f6bf5324f97ce48165ee0a4064ca1da951128719b946cf2a48d.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 82190763a960bced7b82708ed585d179b5d77d9afa3baca2d80a2e30c7eb71d9.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 8329d2bf3e63e61c5981a9e16bb88a793a25b100e557f88042df0141782c526a.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 85e89c780d381670aa148511abca32fb71294f6a52747ef14d763e94ece9af14.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 88902cd1620a84dd55ac5212ef3b201701d2eda8fe856ad093a593a9995b3f2c.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 89517a1f21e4efe4d159e8de10e784de7695580aca7cebdcb3e54cc9487a35b2.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 898349432858be978d9e9e1df267d063fcf6dab17bfb7250ec093c88e63085ee.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8a1dac7487163a8cdc625b618defe761f73854c463c01a742c52156b399c1991.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8a6dae8286ae925bec1b80d6bd46e19774e02a7b3959ba2db76b6d4e64141333.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 8aee7b9045f8e52c88b90a1ee80c9288354b231d99d120eaedd1559b7597f421.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 3, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 8f52677f4b61ba22cb9e5633c9a0a331301fbb8b2647a99d5eb4125bfb1435d5.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 32 1, .triangle 23 0, .gapLower 1 4, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0]

-- Cycle fingerprint 91a6e99fcfb1298ef2b56cf89c3d2a283ff08fbd2421fbfde963c03137548d41.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 92e99db582c3452ef6ae8a4825c8a902482e2ec57afdb55e1dbbfc95f9b6f7e4.
def localCycle00079 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 9b786d8e721a49ddf038c99d84d3f2a1d6f49a7a21f1f5d54f39bf525cd66678.
def localCycle00080 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9c21c43a41f68d3019aeccbd54e9c08771ce309188cc7cacf45a440299338772.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 1]

-- Cycle fingerprint 9e8c9648485ef497326ab3ca267473d7fb906990d527e7bbe4aca08f4b126c17.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 9ea40b52308d1d2757e179369f0326160c990ac1b5a5d0fc3723772a94ef65be.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 9f4dcba8128f646f3c31435dc88a5df62ce932c30c99ed83f21c5ab88dd51e23.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint a0ecede5a72af281fe893b56b7f3b0b95de164346b75fc9295735fb3f7036189.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4]

-- Cycle fingerprint a25f537688ffd8b330cf015a8f4b197dfb8fee229c2c1b674357873cdf0c509c.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 30 1, .triangle 17 2, .triangle 3 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint a295ac0868ff8905b93ba3e204102a9c825cabbe9bcea63ad588d604e2a76d48.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a2ff5cb3755d1e32664f633c7ad4da4da6dc55fd542d487509e2748060c7807a.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a33a4b50a4ea9f4ac455d61a65f0a6612f6b7b22e50063e296e84cc530c802fd.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ada36d1d438a04a46ba8c84a44901706bf64c8e6f6ae329c496097b81dbdefe9.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint ae9bc8eb87b21733e193b3c4d29d3ffc354c19db60869a22b552120f4db60f6c.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![-1, 0, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 13 0, .gapLower 0 4, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint af3ae010e5bc494eb14ab4831dea5d0e67bd4553103a9e9bf0cd17b696edb02a.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -3, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint b305872a138359cd5a713e7a4920ec11db4e72a5b62f01ba5244f6b8fa3bce60.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint b404fa61b60072a48696ea50512f3262bdb1f61241c0f33716ea9f40bf9db521.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 1 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b674a67a884f7d6f237380ad04720598ca7960d0ba3b80a49b8b12ea92150ff1.
def localCycle00095 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint b74cc5c581e7bc20213bfdf613ca41f18e862f9d82eb3538726eabf87daade9e.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint b7fbf11e90af644cfef90d75c90439bab7d3ddbda47735ad50c124cc5d1b6c35.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint bd64bbd51a8385461cc1b281446ddea96297339977d75937346b8c69baf377a4.
def localCycle00098 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c07bbb447ada9d622d401e7c87e95665815d8e4d560913a5b9df7be857d7d0ac.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c29ed41ac1e33e2d3be9b8233954e82105c26c9c0e5719587f2382950998673d.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint c5a4ff070cc60c4bb28c30e237c3af8d0df4d0b8cf9d44331e21ebf8af39e5e4.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 19 1, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint c8ee3599f91d2bfb43d74e89789df852988ba2bfb8f227255138c86fa6a0aa5e.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cd9c75a71d03ef2ceaf2a2e7f4c5d81e808418da7719e8b6f3aec928b5b36768.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ce17616a563662da2130e87ce541d74cc5645f68783f088acc91d09afed838ee.
def localCycle00104 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint ce923181c8c2bbf6e8da304d722dfa06619032e728efceaa1860261a61e297c1.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d2525126d162a0d1ca7b9de6e2b6010a9a9b24ed9f5de9028466bf9eba7b58b0.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint d4e61c66995aaa7ff56786efc40da203038f22e1e2031636c0725f48fb8722b0.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint d54ab77c5d0ca147ebdd73537b19fe22850c66bd43d6c37212d769d89e816dc7.
def localCycle00108 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3]
    constant := ![0, -2, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 1]

-- Cycle fingerprint d55da5e4224db7ec2cd121e1bb48fa994a751d60a46035dc10175f247337c590.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint d7ec84da5800cfc84971d43c5e07360e008ce90d5b12657cb5f80dda1a514484.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d98285c430cc193f80cff46aa79d322f0de93d09b87b3fdd7b5c492bdd719355.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 1]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00112 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dafb596385437a575040e6bdaa3b241a470423804b6b202f3c00f9666baec3ce.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dbe791fc41ede5fce55370ca32ad89bc6fde05a05f9d217abb7febb5dff00fb7.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint de34772163b01bab84ea6097e4556815d7ccd216de6ca4cb85fbd43e07578633.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, 0, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint df0e6ff46665080406aa72192653eacf1a60ce322489112ae2d6e3b0ad409649.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint dfd09ff3ec7b64734f6438efe6f15547130bc21d9c6bc6c82f75d6b36dedb6d2.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint e1978c894fa3d0aee705daeee4bb900e362965d06ecb1951f46599230532153c.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint e30bf2910c175cb62dc433a85694c5da210b559b0a6488bc7540c3a6ef7ce50b.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, -1, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e3899075cb714a78cdeae14acb77d057b707856b6eea2d7da17f6905e9ebcbd2.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint e41ed6e8d383f4976fac93d375bf7f6e7df524009e6548beffdfc13774efd014.
def localCycle00121 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 4, .triangle 1 0, .triangle 3 0, .triangle 20 1]

-- Cycle fingerprint e447304167fa630aa16b52cce670e5fd499b90ef7882f7d18e5083e0ff9fe237.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint e449b6228bc7e42b78ca25fcdd2e1f2314982dc709f8c538e2e35874eedf9cf0.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint e74a24393bcdd219837800b1d24729f3fe3c03af3b4bd3fcd7a15ad74c56db07.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint eb231b717d9bad73fbd0d75d3d0b821a820660cba8c9fe3a4fdb6e5b16ba6e7b.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -1, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint ee95785255b16eef7a4d51f0463e31264c6551abaac1d5c69eea3c87a4e0b4f3.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint f06a04cfa0f808e014f9b2d6cf37f8a659940da4669dbe77190c754afc050083.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f8d1319ee1f3071c5426431a7388475a11fbb642bcc5771ac1a016336add88ed.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint fa77864d27e59d451d8ca794d64d5b74bdfeecb62c41a18295d39addd5052387.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint faea07e34941b38a26efc0b023ba17ad0a5c5108b2b45cfffce8379ef80058ba.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fb5b890848b93299bad1078920f10aef944bcfd8c3482c181ea2d64b48c7c1f1.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint fe0208ce090918b65597bda6cef27b4c252c439b0c2c069926144889096d0b8f.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fe61b6a4256500279f6dba4d9d8a6b926841533f864d25107827bdf98ddc1cc1.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2]

-- Cycle fingerprint ffd2f707fd3eb72b8233e412693bfe1a76af37a3210530f14fb42c510a17d069.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

def library : Library := fun id => if id < 67 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 50 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))))) else (if id < 58 then (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 62 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))))) else (if id < 101 then (if id < 84 then (if id < 75 then (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 92 then (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))))) else (if id < 118 then (if id < 109 then (if id < 105 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))) else (if id < 126 then (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 130 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 0, 1, 2]], proof := .tail 126 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12544)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 60 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12545)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12546)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 1, 2, 0]], proof := .tail 56 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12547)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 70 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12548)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 57 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12549)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 50 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12550)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 21 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12551)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 3, 4, 6], ![0, 1, 5, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 22 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12552)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 3, 4, 6], ![0, 1, 5, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 105 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12553)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 43 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12554)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 120 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12555)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 83 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12556)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 80 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12557)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 31 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12558)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 120 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12559)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 83 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12560)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 30 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12561)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 30 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12562)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 53 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12563)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 3, 6, 4], ![0, 1, 5, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 32 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12564)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 6, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 49 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12565)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 5, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 13 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12566)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 30 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12567)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 30 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12568)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 30 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12569)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 0 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12570)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 53 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12571)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 53 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12572)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 41 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12573)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 118 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12574)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 71 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12575)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 44 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12576)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 44 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12577)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12578)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 90 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12579)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 90 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12580)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 99 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12581)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 66 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12582)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 14 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12583)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 67 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12584)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 77 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12585)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 17 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12586)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 68 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12587)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 120 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12588)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 17 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12589)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 12 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12590)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 83 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12591)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 131 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12592)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 28 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12593)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 89 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12594)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 103 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12595)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 17 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12596)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 98 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12597)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 13 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12598)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 25 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12599)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 28 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12600)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 28 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12601)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 1 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12602)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 110 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12603)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 123 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12604)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 110 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12605)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 110 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12606)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 110 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12607)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 123 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12608)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 123 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12609)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12610)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12611)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 91 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12612)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 93 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12613)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 40 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12614)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 45 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12615)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 10 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12616)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 96 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12617)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 15 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12618)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 15 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12619)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 15 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12620)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 61 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12621)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![54, 115, 46, 36, 92, 88, 47, 64, 4, 16, 65, 8, 29, 7, 76, 42, 52, 51, 116, 20, 78, 108, 18, 3, 111, 107, 19, 79]) }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12622)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 10 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12623)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 15 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12624)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 96 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12625)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 15 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12626)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 61 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12627)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![59, 33, 46, 62, 63, 119, 47, 86, 133, 125, 11, 94, 29, 114, 134, 58, 95, 51, 35, 128, 100, 55, 97, 75, 101, 109, 81, 104]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12628)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 13 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12629)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 25 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12630)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 27 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12631)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 112 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12632)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 48 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12633)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 73 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12634)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 112 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12635)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 72 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12636)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 9 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12637)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 112 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12638)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 130 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12639)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 87 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12640)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 112 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12641)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 84 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12642)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 122 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12643)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 106 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12644)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 85 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12645)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 121 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12646)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 127 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12647)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 23 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12648)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 5 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12649)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 69 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12650)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 23 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12651)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 5 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12652)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 24 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12653)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 4, 6], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 1, 0, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 6 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12654)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 6 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12655)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 129 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12656)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 3, 6, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 6 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12657)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 129 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12658)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 124 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12659)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 5, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 117 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12660)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 13 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12661)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 34 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12662)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 113 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12663)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 82 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12664)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 0, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 2 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12665)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 5, 6, 0, 3, 4], ![1, 6, 0, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 39 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12666)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 113 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12667)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 82 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12668)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 3, 4], ![1, 6, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 2 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12669)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 0, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 102 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12670)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 3, 4], ![6, 1, 0, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 74 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12671)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (12544 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 12544 ≤ id.val) (hhigh : id.val < 12672) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 12544)) = true := by
  let j : Fin 128 := ⟨id.val - 12544, by omega⟩
  have hsum : 12544 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (12544 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard098
