import tests.h62.item2.«audit-v07-lowering».CanonicalConversionReview
import Solidity.Lowering.V07.AddressConversions
import Solidity.Lowering.V07.AddressQualifiers
import Solidity.Lowering.V07.EnumConversions
import Solidity.Lowering.V07.EnumSignedCasts
import Solidity.Lowering.V07.EnumSignedWord
import Solidity.Lowering.V07.EnumUnsignedCasts
import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.V07.IntegralRationalConstants
import Solidity.Lowering.V07.SignedEnumTransport
import Solidity.Lowering.V07.SignedWidthCasts
import Solidity.Lowering.V07.UdvtAssignment
import Solidity.Lowering.V07.UnsignedCasts
import Solidity.Lowering.V07.UnsignedEnumGuard
import Solidity.Lowering.V07.UnsignedWidthCasts

/-!
Guarded regression: the mapFree transport must retain all nineteen frozen header
binders, including widths/ranges/nominal identities. V0 uses frozen operators;
V1 uses current interfaces. No production interface or strict baseline changes.
These are conversion predicates, not compiler success or whole-program results.
-/
set_option autoImplicit false

namespace Solidity.H62.AuditV07.CanonicalHeaderPairs
open Solidity.Source
open Solidity.H62.AuditV07.CanonicalConversionReview
open Solidity.Backend.PrimitivePackets.Constants.H57ConversionTransport (implicitV0)

section
open Solidity.Lowering.V07.AddressConversions
namespace V0.AddressConversions
theorem allowed_from (E : Source.Env) : (explicitV0 E.isBase (Source.STy.int ty) (.address false)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int ty) (Scalar.address false)).trans
    (Solidity.Lowering.V07.AddressConversions.allowed_from E)
end V0.AddressConversions
namespace V1.AddressConversions
theorem allowed_from (E : Source.Env) : (Source.STy.int ty).explicit E.isBase E.mapFree (.address false) = true :=
  Solidity.Lowering.V07.AddressConversions.allowed_from E
end V1.AddressConversions
end
#print axioms V0.AddressConversions.allowed_from
#print axioms V1.AddressConversions.allowed_from

section
open Solidity.Lowering.V07.AddressConversions
namespace V0.AddressConversions
theorem allowed_to (E : Source.Env) : (explicitV0 E.isBase (Source.STy.address false) (.int ty)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.address false) (Scalar.int ty)).trans
    (Solidity.Lowering.V07.AddressConversions.allowed_to E)
end V0.AddressConversions
namespace V1.AddressConversions
theorem allowed_to (E : Source.Env) : (Source.STy.address false).explicit E.isBase E.mapFree (.int ty) = true :=
  Solidity.Lowering.V07.AddressConversions.allowed_to E
end V1.AddressConversions
end
#print axioms V0.AddressConversions.allowed_to
#print axioms V1.AddressConversions.allowed_to

section
open Solidity.Lowering.V07.AddressConversions
namespace V0.AddressConversions
theorem direct_int_rule (E : Source.Env) (t : Source.IntTy) (p : Bool) :
    (explicitV0 E.isBase (Source.STy.int t) (.address p)) = (!p && !t.signed && t.bits == 160) :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int t) (Scalar.address p)).trans
    (Solidity.Lowering.V07.AddressConversions.direct_int_rule E t p)
end V0.AddressConversions
namespace V1.AddressConversions
theorem direct_int_rule (E : Source.Env) (t : Source.IntTy) (p : Bool) :
    (Source.STy.int t).explicit E.isBase E.mapFree (.address p) = (!p && !t.signed && t.bits == 160) :=
  Solidity.Lowering.V07.AddressConversions.direct_int_rule E t p
end V1.AddressConversions
end
#print axioms V0.AddressConversions.direct_int_rule
#print axioms V1.AddressConversions.direct_int_rule

section
open Solidity.Lowering.V07.AddressQualifiers
namespace V0.AddressQualifiers
theorem allowed_erase (E : Source.Env) (p : Bool) :
    (explicitV0 E.isBase (Source.STy.address p) (.address false)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.address p) (Scalar.address false)).trans
    (Solidity.Lowering.V07.AddressQualifiers.allowed_erase E p)
end V0.AddressQualifiers
namespace V1.AddressQualifiers
theorem allowed_erase (E : Source.Env) (p : Bool) :
    (Source.STy.address p).explicit E.isBase E.mapFree (.address false) = true :=
  Solidity.Lowering.V07.AddressQualifiers.allowed_erase E p
end V1.AddressQualifiers
end
#print axioms V0.AddressQualifiers.allowed_erase
#print axioms V1.AddressQualifiers.allowed_erase

section
open Solidity.Lowering.V07.EnumConversions
namespace V0.EnumConversions
theorem allowed_from (E : Source.Env) (d : Source.DeclName) :
    (explicitV0 E.isBase (Source.STy.int .u256) (.enum d)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int .u256) (Scalar.enum d)).trans
    (Solidity.Lowering.V07.EnumConversions.allowed_from E d)
end V0.EnumConversions
namespace V1.EnumConversions
theorem allowed_from (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.int .u256).explicit E.isBase E.mapFree (.enum d) = true :=
  Solidity.Lowering.V07.EnumConversions.allowed_from E d
end V1.EnumConversions
end
#print axioms V0.EnumConversions.allowed_from
#print axioms V1.EnumConversions.allowed_from

section
open Solidity.Lowering.V07.EnumConversions
namespace V0.EnumConversions
theorem allowed_to (E : Source.Env) (d : Source.DeclName) :
    (explicitV0 E.isBase (Source.STy.enum d) (.int .u256)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.enum d) (Scalar.int .u256)).trans
    (Solidity.Lowering.V07.EnumConversions.allowed_to E d)
end V0.EnumConversions
namespace V1.EnumConversions
theorem allowed_to (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int .u256) = true :=
  Solidity.Lowering.V07.EnumConversions.allowed_to E d
end V1.EnumConversions
end
#print axioms V0.EnumConversions.allowed_to
#print axioms V1.EnumConversions.allowed_to

section
open Solidity.Lowering.V07.EnumSignedCasts
open Solidity.Lowering.V07.SignedWidthCasts (ty)
namespace V0.EnumSignedCasts
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.enum d) (.int (ty bits width))) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.enum d) (Scalar.int (ty bits width))).trans
    (Solidity.Lowering.V07.EnumSignedCasts.allowed E d bits width)
end V0.EnumSignedCasts
namespace V1.EnumSignedCasts
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int (ty bits width)) = true :=
  Solidity.Lowering.V07.EnumSignedCasts.allowed E d bits width
end V1.EnumSignedCasts
end
#print axioms V0.EnumSignedCasts.allowed
#print axioms V1.EnumSignedCasts.allowed

section
open Solidity.Lowering.V07.EnumSignedWord
open Solidity.Lowering.V07.WordCasts (signed)
namespace V0.EnumSignedWord
theorem allowed (E : Source.Env) (d : Source.DeclName) :
    (explicitV0 E.isBase (Source.STy.enum d) (.int signed)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.enum d) (Scalar.int signed)).trans
    (Solidity.Lowering.V07.EnumSignedWord.allowed E d)
end V0.EnumSignedWord
namespace V1.EnumSignedWord
theorem allowed (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int signed) = true :=
  Solidity.Lowering.V07.EnumSignedWord.allowed E d
end V1.EnumSignedWord
end
#print axioms V0.EnumSignedWord.allowed
#print axioms V1.EnumSignedWord.allowed

section
open Solidity.Lowering.V07.EnumUnsignedCasts
open Solidity.Lowering.V07.UnsignedNarrowing (ty)
namespace V0.EnumUnsignedCasts
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.enum d) (.int (ty bits width))) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.enum d) (Scalar.int (ty bits width))).trans
    (Solidity.Lowering.V07.EnumUnsignedCasts.allowed E d bits width)
end V0.EnumUnsignedCasts
namespace V1.EnumUnsignedCasts
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int (ty bits width)) = true :=
  Solidity.Lowering.V07.EnumUnsignedCasts.allowed E d bits width
end V1.EnumUnsignedCasts
end
#print axioms V0.EnumUnsignedCasts.allowed
#print axioms V1.EnumUnsignedCasts.allowed

section
open Solidity.Lowering.V07.IntegerConstants
namespace V0.IntegerConstants
theorem allowed (E : Source.Env) (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (implicitV0 E.isBase (Source.STy.rational (Source.Q.ofInt z)) (.int t)) = true :=
  (implicit_scalar_agrees E.isBase E.mapFree (Scalar.rational (Source.Q.ofInt z)) (Scalar.int t)).trans
    (Solidity.Lowering.V07.IntegerConstants.allowed E t z bound)
end V0.IntegerConstants
namespace V1.IntegerConstants
theorem allowed (E : Source.Env) (t : Source.IntTy) (z : Int) (bound : t.lo ≤ z ∧ z ≤ t.hi) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = true :=
  Solidity.Lowering.V07.IntegerConstants.allowed E t z bound
end V1.IntegerConstants
end
#print axioms V0.IntegerConstants.allowed
#print axioms V1.IntegerConstants.allowed

section
open Solidity.Lowering.V07.IntegerConstants
namespace V0.IntegerConstants
theorem not_allowed (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    (implicitV0 E.isBase (Source.STy.rational (Source.Q.ofInt z)) (.int t)) = false :=
  (implicit_scalar_agrees E.isBase E.mapFree (Scalar.rational (Source.Q.ofInt z)) (Scalar.int t)).trans
    (Solidity.Lowering.V07.IntegerConstants.not_allowed E t z outside)
end V0.IntegerConstants
namespace V1.IntegerConstants
theorem not_allowed (E : Source.Env) (t : Source.IntTy) (z : Int)
    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :
    (Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase E.mapFree (.int t) = false :=
  Solidity.Lowering.V07.IntegerConstants.not_allowed E t z outside
end V1.IntegerConstants
end
#print axioms V0.IntegerConstants.not_allowed
#print axioms V1.IntegerConstants.not_allowed

section
open Solidity.Lowering.V07.IntegralRationalConstants
namespace V0.IntegralRationalConstants
theorem allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    (implicitV0 E.isBase (Source.STy.rational q) (.int t)) = true :=
  (implicit_scalar_agrees E.isBase E.mapFree (Scalar.rational q) (Scalar.int t)).trans
    (Solidity.Lowering.V07.IntegralRationalConstants.allowed E q t h)
end V0.IntegralRationalConstants
namespace V1.IntegralRationalConstants
theorem allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (h : q.FitsInt t) :
    (Source.STy.rational q).implicit E.isBase E.mapFree (.int t) = true :=
  Solidity.Lowering.V07.IntegralRationalConstants.allowed E q t h
end V1.IntegralRationalConstants
end
#print axioms V0.IntegralRationalConstants.allowed
#print axioms V1.IntegralRationalConstants.allowed

section
open Solidity.Lowering.V07.IntegralRationalConstants
namespace V0.IntegralRationalConstants
theorem not_allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (refused : ¬ q.FitsInt t) :
    (implicitV0 E.isBase (Source.STy.rational q) (.int t)) = false :=
  (implicit_scalar_agrees E.isBase E.mapFree (Scalar.rational q) (Scalar.int t)).trans
    (Solidity.Lowering.V07.IntegralRationalConstants.not_allowed E q t refused)
end V0.IntegralRationalConstants
namespace V1.IntegralRationalConstants
theorem not_allowed (E : Source.Env) (q : Source.Q) (t : Source.IntTy) (refused : ¬ q.FitsInt t) :
    (Source.STy.rational q).implicit E.isBase E.mapFree (.int t) = false :=
  Solidity.Lowering.V07.IntegralRationalConstants.not_allowed E q t refused
end V1.IntegralRationalConstants
end
#print axioms V0.IntegralRationalConstants.not_allowed
#print axioms V1.IntegralRationalConstants.not_allowed

section
open Solidity.Lowering.V07.SignedEnumTransport
open Solidity.Lowering.V07.SignedWidthCasts (ty)
namespace V0.SignedEnumTransport
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.int (ty bits width)) (.enum d)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int (ty bits width)) (Scalar.enum d)).trans
    (Solidity.Lowering.V07.SignedEnumTransport.allowed E d bits width)
end V0.SignedEnumTransport
namespace V1.SignedEnumTransport
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty bits width)).explicit E.isBase E.mapFree (.enum d) = true :=
  Solidity.Lowering.V07.SignedEnumTransport.allowed E d bits width
end V1.SignedEnumTransport
end
#print axioms V0.SignedEnumTransport.allowed
#print axioms V1.SignedEnumTransport.allowed

section
open Solidity.Lowering.V07.SignedWidthCasts
namespace V0.SignedWidthCasts
theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.int (ty fromBits fromValid)) (.int (ty bits valid))) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int (ty fromBits fromValid)) (Scalar.int (ty bits valid))).trans
    (Solidity.Lowering.V07.SignedWidthCasts.allowed fromBits fromValid E bits valid)
end V0.SignedWidthCasts
namespace V1.SignedWidthCasts
theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty fromBits fromValid)).explicit E.isBase E.mapFree (.int (ty bits valid)) = true :=
  Solidity.Lowering.V07.SignedWidthCasts.allowed fromBits fromValid E bits valid
end V1.SignedWidthCasts
end
#print axioms V0.SignedWidthCasts.allowed
#print axioms V1.SignedWidthCasts.allowed

section
open Solidity.Lowering.V07.UdvtAssignment
namespace V0.UdvtAssignment
theorem nominal_implicit (E : Source.Env) (d e : Source.DeclName) :
    (implicitV0 E.isBase (Source.STy.udvt d) (.udvt e)) = (d == e) :=
  (implicit_scalar_agrees E.isBase E.mapFree (Scalar.udvt d) (Scalar.udvt e)).trans
    (Solidity.Lowering.V07.UdvtAssignment.nominal_implicit E d e)
end V0.UdvtAssignment
namespace V1.UdvtAssignment
theorem nominal_implicit (E : Source.Env) (d e : Source.DeclName) :
    (Source.STy.udvt d).implicit E.isBase E.mapFree (.udvt e) = (d == e) :=
  Solidity.Lowering.V07.UdvtAssignment.nominal_implicit E d e
end V1.UdvtAssignment
end
#print axioms V0.UdvtAssignment.nominal_implicit
#print axioms V1.UdvtAssignment.nominal_implicit

section
open Solidity.Lowering.V07.UnsignedCasts
open Solidity.Lowering.V07.UnsignedNarrowing (ty)
namespace V0.UnsignedCasts
theorem allowed (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.int .u256) (.int (ty bits valid))) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int .u256) (Scalar.int (ty bits valid))).trans
    (Solidity.Lowering.V07.UnsignedCasts.allowed E bits valid)
end V0.UnsignedCasts
namespace V1.UnsignedCasts
theorem allowed (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int .u256).explicit E.isBase E.mapFree (.int (ty bits valid)) = true :=
  Solidity.Lowering.V07.UnsignedCasts.allowed E bits valid
end V1.UnsignedCasts
end
#print axioms V0.UnsignedCasts.allowed
#print axioms V1.UnsignedCasts.allowed

section
open Solidity.Lowering.V07.UnsignedEnumGuard
open Solidity.Lowering.V07.UnsignedNarrowing (ty)
namespace V0.UnsignedEnumGuard
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.int (ty bits width)) (.enum d)) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int (ty bits width)) (Scalar.enum d)).trans
    (Solidity.Lowering.V07.UnsignedEnumGuard.allowed E d bits width)
end V0.UnsignedEnumGuard
namespace V1.UnsignedEnumGuard
theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty bits width)).explicit E.isBase E.mapFree (.enum d) = true :=
  Solidity.Lowering.V07.UnsignedEnumGuard.allowed E d bits width
end V1.UnsignedEnumGuard
end
#print axioms V0.UnsignedEnumGuard.allowed
#print axioms V1.UnsignedEnumGuard.allowed

section
open Solidity.Lowering.V07.UnsignedWidthCasts
open Solidity.Lowering.V07.UnsignedNarrowing (ty)
namespace V0.UnsignedWidthCasts
theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (explicitV0 E.isBase (Source.STy.int (ty fromBits fromValid)) (.int (ty bits valid))) = true :=
  (explicit_scalar_agrees E.isBase E.mapFree (Scalar.int (ty fromBits fromValid)) (Scalar.int (ty bits valid))).trans
    (Solidity.Lowering.V07.UnsignedWidthCasts.allowed fromBits fromValid E bits valid)
end V0.UnsignedWidthCasts
namespace V1.UnsignedWidthCasts
theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty fromBits fromValid)).explicit E.isBase E.mapFree (.int (ty bits valid)) = true :=
  Solidity.Lowering.V07.UnsignedWidthCasts.allowed fromBits fromValid E bits valid
end V1.UnsignedWidthCasts
end
#print axioms V0.UnsignedWidthCasts.allowed
#print axioms V1.UnsignedWidthCasts.allowed

end Solidity.H62.AuditV07.CanonicalHeaderPairs
