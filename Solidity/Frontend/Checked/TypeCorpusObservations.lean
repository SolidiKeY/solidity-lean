import Solidity.Frontend.Checked.TypeExampleCore

/-! Named copies of the two original corpus predicates. Naming the predicates
avoids elaborator reduction of a closed parser while matching proof rewrites. -/

namespace Solidity.Frontend.Checked.TypeCorpusCertificates

open Solidity.Source

def profileObservation (s : String) : Bool :=
  match parse (ascii s) with
  | .ok u => u.rejections.isEmpty
  | .error _ => false

def roundtripObservation (s : String) : Bool :=
  reprintFingerprint s == fingerprint (parseWithLayout (ascii s)) &&
    (reprintFingerprint s).isSome

end Solidity.Frontend.Checked.TypeCorpusCertificates
