import Solidity.Calculus.Problem

/-!
# Storage declarations certified by their contract

The checks apply to record literals as well as `contract!{ … }`, and to
record updates. Generic clients use the contract's evidence directly.
-/

namespace Solidity.Examples.ContractTypes

/-- Empty storage is a valid contract, including the `Inhabited` default. -/
example : (default : Contract).vars = [] := rfl

/-- Storage roots cannot repeat a name, even at the same type. -/
example : True := by
  fail_if_success
    have bad : Contract := { vars := [("x", .uint), ("x", .uint)] }
  trivial

/-- Conflicting declarations cannot hide behind the first lookup result. -/
example : True := by
  fail_if_success
    have bad : Contract := { vars := [("x", .uint), ("x", .bool)] }
  trivial

/-- A raw record cannot declare an unknown struct as a storage root. -/
example : True := by
  fail_if_success
    have bad : Contract := { vars := [("x", .ref (.struct "Missing"))] }
  trivial

/-- Type validity reaches through arrays and mappings. -/
example : True := by
  fail_if_success
    have bad : Contract :=
      { vars := [("xs", .ref (.array (.ref (.mapping .uint (.ref (.struct "Missing"))))))] }
  trivial

/-- Updating a contract's roots requires new evidence for the new declaration. -/
example (_C : Contract) : True := by
  fail_if_success
    have bad : Contract :=
      { _C with
        vars := [("x", .uint), ("x", .bool)]
        vars_ok := by decide
        vars_nodup := by decide }
  trivial

/-- Metadata updates retain the same certified storage declaration. -/
example (C : Contract) : ({ C with evalOrder := EvalOrder.viaIR } : Contract).vars = C.vars := rfl

/-- Replacing the declaration supplies new certificates for its new roots. -/
example (C : Contract) :
    ({ C with
       vars := [("x", .uint)]
       vars_ok := by decide
       vars_nodup := by decide } : Contract).vars = [("x", .uint)] := rfl

/-- Symbolic declarations provide their evidence explicitly. -/
example (vs : List (Name × Ty)) (ho : vs.all (fun nt => nt.2.okDeep) = true)
    (hn : Semantics.nodupKeysB vs = true) :
    ({ vars := vs, vars_ok := ho, vars_nodup := hn } : Contract).vars = vs := rfl

/-- The Solidity spelling enforces the same uniqueness requirement. -/
example : True := by
  fail_if_success
    have bad : Contract := contract!{ uint x; bool x; }
  trivial

/-- Encoded structs retain their validity certificates. -/
def Nested : Contract := contract!{
  struct Point { uint x; bool marked; }
  struct Shape { Point[] points; mapping(uint => Point) named; }
  Shape shape;
}

/-- A symbolic struct definition is a valid contract without computation. -/
example (s : Name) : (Contract.ofStruct s).vars.all (fun nt => nt.2.okDeep) = true :=
  (Contract.ofStruct s).vars_ok

/-- Root types inherit validity without a separate contract hypothesis. -/
example (C : Contract) {r : Name} {T : Ty} (h : C.rootType r = some T) : T.okDeep = true :=
  C.root_okDeep h

/-- Reachability needs only the value's slot bounds; the contract certifies
its declaration for every client. -/
example (C : Contract) (st : Storage C) (hf : st.Fits) :
    st.wtB = true ↔ Reachable C st :=
  wt_iff_reachable hf

/-- Initial well-formedness is available for every contract. -/
example (C : Contract) : holds (State.init C) (Fml.wt C) := initStorage_wt

end Solidity.Examples.ContractTypes
