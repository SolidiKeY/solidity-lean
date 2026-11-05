import SolidityBridge.PrecompileAgreement.Controls

/-! Computed core vectors, not cryptographic implementation equality proofs.
The arbitrary-input agreement theorems live in the imported modules. -/
namespace SolidityBridge.PrecompileAgreement.BoundaryVectors
open Solidity.Precompiles Solidity.Roadmap.Evm
open SolidityBridge.PrecompileAgreement.Controls

#guard [0,127,128,129].map (fun n => ecrecover (zeros n)) == List.replicate 4 (some [])
#guard Bn254.add [] == some (zeros 64)
#guard Bn254.mul [] == some (zeros 64)
#guard (Bn254.pairing (word Bn254.p ++ zeros 160)).isNone

def modHeader (b e m : Nat) : Bytes := word b ++ word e ++ word m
#guard [1024,1025].map (fun n => (Modexp.modexp (modHeader n 0 0)).isSome) == [true,false]
#guard [0,31,32,33].map (fun e => Modexp.modexp (modHeader 1 e 1 ++ [3] ++ zeros e ++ [5])) ==
  List.replicate 4 (some [1])
#guard Modexp.modexp (modHeader 33 1 1 ++ [1] ++ zeros 31 ++ [1,1,3]) == some [2]

#guard [255,256,257].map (fun n => (Bls12381.g1Add (zeros n)).isSome) == [false,true,false]
#guard [511,512,513].map (fun n => (Bls12381.g2Add (zeros n)).isSome) == [false,true,false]
#guard [0,159,160,161,320].map (fun n => (Bls12381.g1Msm (zeros n)).isSome) == [false,false,true,false,true]
#guard [0,287,288,289,576].map (fun n => (Bls12381.g2Msm (zeros n)).isSome) == [false,false,true,false,true]
#guard [0,383,384,385,768].map (fun n => (Bls12381.pairing (zeros n)).isSome) == [false,false,true,false,true]
#guard [63,64,65].map (fun n => (Bls12381.mapFpToG1 (zeros n)).isSome) == [false,true,false]
#guard [127,128,129].map (fun n => (Bls12381.mapFp2ToG2 (zeros n)).isSome) == [false,true,false]
#guard [Bls12381.p-1,Bls12381.p].map (fun x => (Bls12381.decodeFp ((toBE 64 x).map UInt8.toNat)).isSome) == [true,false]
#guard [Bls12381.p-1,Bls12381.p].map (fun x => (Bls12381.decodeFp2 ((zeros 64 ++ toBE 64 x).map UInt8.toNat)).isSome) == [true,false]
#guard (Bls12381.g1Add (toBE 64 Bls12381.p ++ zeros 192)).isNone
#guard (Bls12381.g2Add (toBE 64 Bls12381.p ++ zeros 448)).isNone
#guard [159,160,161].map (fun n => P256.p256Verify (zeros n)) == List.replicate 3 (some [])
#guard [0,P256.n].all (fun v =>
  P256.p256Verify (word 0 ++ word v ++ word 1 ++ zeros 64) == some [] &&
  P256.p256Verify (word 0 ++ word 1 ++ word v ++ zeros 64) == some [])
#guard P256.decodeKey 0 0 |>.isNone
#guard (Bls12381.decodeG1Sub ((zeros 64 ++ toBE 64 2).map UInt8.toNat)).isNone
#guard (Bls12381.g1Msm (zeros 64 ++ toBE 64 2 ++ word 1)).isNone
#guard (Bls12381.pairing (zeros 64 ++ toBE 64 2 ++ zeros 256)).isNone

open Bls12381 in
def rawG2 := isoMap (Iso.iso3XNum.map f2) (Iso.iso3XDen.map f2) (Iso.iso3YNum.map f2)
  (Iso.iso3YDen.map f2) (sswu (f2 Iso.iso3A) (f2 Iso.iso3B) (f2 Iso.iso3Z) sqrtFp2 sgn0Fp2 (f2 (0,0)))
#guard (Bls12381.decodeG2 ((Bls12381.encodeG2 rawG2).map UInt8.toNat)).isSome
#guard (Bls12381.decodeG2Sub ((Bls12381.encodeG2 rawG2).map UInt8.toNat)).isNone
#guard (Bls12381.g2Msm (Bls12381.encodeG2 rawG2 ++ word 1)).isNone
#eval "BOUNDARY_VECTORS_PASS"
end SolidityBridge.PrecompileAgreement.BoundaryVectors
