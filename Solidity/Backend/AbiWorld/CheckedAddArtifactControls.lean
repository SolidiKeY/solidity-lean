import Solidity.Backend.AbiWorld.CheckedAddArtifact
namespace Solidity.Backend.AbiWorld.CheckedAddArtifactControls
open CheckedAddArtifact

theorem at_zero : (compile 8 0 0).isSome := compiles_bounded 8 0 0 (by decide +kernel)
theorem relocated : (compile 8 32 5).isSome := compiles_bounded 8 32 5 (by decide +kernel)

theorem witnessed : ∃ out, compile 8 0 0=some out :=
 Option.isSome_iff_exists.mp at_zero

def code (base label : Nat) : List UInt8 :=
 ((compile 8 base label).map (fun out=>encode out.code)).getD []

theorem populated_artifact {out : Assembled Empty} (assembled : compile 8 0 0=some out) :
 out.code≠[] := by
 obtain ⟨j,imm,_,dest,_,_⟩ := conditional_target 8 0 0 assembled
 intro empty
 rw [empty] at dest
 cases dest

theorem wrong_label (address label : Nat) :
 (items address label)[6]?≠some (.pushTag (label+1)) := by
 rw [condition_ref]
 intro equal
 have labels : label=label+1 := by
  simpa only [Option.some.injEq,Item.pushTag.injEq] using equal
 omega

def jsonBytes (bs : List UInt8) : String :=
 "[" ++ String.intercalate "," (bs.map (fun b=>toString b.toNat)) ++ "]"
def jsonNats (ns : List Nat) : String :=
 "[" ++ String.intercalate "," (ns.map toString) ++ "]"
#eval IO.println ("CHECKED_ADD_CODE_ZERO=" ++ jsonBytes (code 0 0))
#eval IO.println ("CHECKED_ADD_CODE_RELOCATED=" ++ jsonBytes (code 32 5))
#eval IO.println ("CHECKED_ADD_DESTINATIONS_ZERO=" ++ jsonNats (jumpdests (code 0 0)))
#eval IO.println ("CHECKED_ADD_DESTINATIONS_RELOCATED=" ++ jsonNats (jumpdests (code 32 5)))
#print axioms expanded
#print axioms compiles
#print axioms conditional_target
#print axioms at_zero
#print axioms relocated
#print axioms witnessed
#print axioms populated_artifact
#print axioms wrong_label
#print axioms item_count
#print axioms compiles_bounded
end Solidity.Backend.AbiWorld.CheckedAddArtifactControls
