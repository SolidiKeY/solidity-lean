import Aesop

import SolidityLean.Field

variable {ValTp IdTp ValSTp IdSTp : Type}

inductive Memory (ValTp ValSTp IdSTp IdTp : Type) where
  | mtm
  | write (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdT ValSTp IdSTp IdTp)
    (fld : FieldSelector ValSTp IdSTp) (val : ValT ValTp ValSTp IdSTp IdTp)
  | add   (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdTp)

namespace Memory

@[simp] def read [DecidableEq ValSTp] [DecidableEq IdSTp] [DecidableEq IdTp]
  [Inhabited ValTp] (mem : Memory ValTp ValSTp IdSTp IdTp) (id : IdT ValSTp IdSTp IdTp)
  (fld : FieldSelector ValSTp IdSTp) : ValT ValTp ValSTp IdSTp IdTp :=
  match mem, id with
  | .mtm, _ => .val default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, ⟨idd, valS⟩ => if pId = idd
    then (match fld with
      | .valS  _ => .val default
      | .idS _ => .id ⟨idd, fld :: valS⟩
      )
    else read mem id fld
