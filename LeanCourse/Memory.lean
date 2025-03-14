import Aesop

import LeanCourse.Field

variable {ValType IdType ValSType IdSType : Type}

inductive Memory (ValType ValSType IdSType IdType : Type) where
  | mtm
  | write (mem : Memory ValType ValSType IdSType IdType) (id : IdT ValSType IdSType IdType) (fld : FieldSelector ValSType IdSType) (val : ValT ValType ValSType IdSType IdType)
  | add   (mem : Memory ValType ValSType IdSType IdType) (id : IdType)

namespace Memory

@[simp] def read [DecidableEq ValSType] [DecidableEq IdSType] [DecidableEq IdType]
  [Inhabited ValType] (mem : Memory ValType ValSType IdSType IdType) (id : IdT ValSType IdSType IdType) (fld : FieldSelector ValSType IdSType) : ValT ValType ValSType IdSType IdType :=
  match mem, id with
  | .mtm, _ => .val default
  | .write mem idM fldM val, _ => if idM = id && fldM = fld then val else read mem id fld
  | .add mem pId, ⟨idd, valS⟩ => if pId = idd
    then (match fld with
      | .valS  _ => .val default
      | .idS _ => .id ⟨idd, fld :: valS⟩
      )
    else read mem id fld
