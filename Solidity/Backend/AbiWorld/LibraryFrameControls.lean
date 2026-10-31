import Solidity.Backend.AbiWorld.LibraryFrameTransport
import Solidity.Backend.AbiWorld.CatchTransport
import Solidity.Backend.AbiWorld.WorldFrames

/-! Actual installed-library consumers with a populated caller heap/frame.
These finite intrinsic controls establish no compiled library/world theorem. -/
namespace Solidity.Backend.AbiWorld.LibraryFrameControls
open ContractWorld LibraryFrameTransport

def C : Contract := { vars := [("saved", .prim .uint)] }
def catalog (_ : Bool) : Contract := C
def addr (n : Nat) (h : n < 2 ^ 160 := by decide +kernel) : Address :=
  ⟨⟨n, by have : n < 2 ^ 256 := Nat.lt_trans h (by decide +kernel)
          exact PrimTy.inRange_uint_of_lt this⟩, by change (n : Int) < (2 : Int) ^ 160; exact_mod_cast h⟩
def self : Handle false := ⟨addr 7⟩
def ctx : Context := { sender := addr 9 }
def world : World catalog := {
  accounts := fun a => if a = addr 7 then some ⟨false, (State.init C).storage⟩
    else if a = addr 8 then some ⟨true, (State.init C).storage⟩ else none,
  funds := fun a => if a = addr 7 then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩,
  roles := fun k => if k then .libraryCode else .contractCode }
def initial : State C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := (),
    selfBalance := ⟨100, by decide +kernel⟩,
    tx := ctx.tx world self.address }
def u {Γ : Ctx} (n : Nat) (h : n < 2 ^ 256 := by decide +kernel) : Val C Γ .uint :=
  .simple (.lit n (PrimTy.inRange_uint_of_lt h))
abbrev Γ : Ctx := [.mem bytesR, .mem bytesR, .val .uint]
def before : Prog C [] Γ :=
  .cons (.assign (.root "saved" rfl) (.val (u 9)))
  (.cons (.transfer (u 10) (u 3))
  (.cons (.declLocal .uint (.user "marker") (some (u 77)))
  (litBytes (.user "older") [161, 0, 178]
  (.cons (.declMem bytesR (.user "alias") (some (.alias (.var .here rfl))) rfl rfl) .nil))))
def start : Out C [] Γ := (before.run initial).toOption.get (by decide +kernel)
attribute [irreducible] start

def pre : World catalog := (world.finish (k := false) self.address start.st).toOption.get (by decide +kernel)
attribute [irreducible] pre

def words : List Word := [⟨12, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨254, by decide +kernel⟩]
def body : Prog C [] [] := .cons (.assign (.root "saved" rfl) (.val (u 12))) .nil
def raw (p : Prog C [] []) (ws : List Word := words) : LibraryTryFrame.RawLibrary catalog false :=
  ⟨⟨true, addr 8, ⟨[], p, fun _ => .ok ws, false⟩⟩, fun _ => ⟨ws, rfl⟩⟩
/-- Actual published primitive binder; trailing raw words are not silently lost. -/
def decode (ws : List Word) : TRes (Word × List Word) := do
  let (env, rest) ← Binders.decodeT (C := C) (H := []) (.snoc .nil .uint (.user "value")) ws
  pure (env.1, rest)
def tailBody (v : Word) : Prog C Γ Γ :=
  .cons (.assignLocal (.there (.there .here)) (.simple (.lit v.1 v.2)))
  (.cons (.transfer (u 10) (u 2)) .nil)

/-- Exact old IDs and complete ordered objects, including the embedded zero. -/
def aliases (σ : State C Γ) : List (Nat × List Int) :=
  ([TEnv.get .here σ.env, TEnv.get (.there .here) σ.env] : List (Option (HRef σ.H bytesR))).filterMap
    (fun r => r.map (fun r => (r.id, (σ.heap.get r : MObj σ.H bytesR).1.map (fun b => b.1))))
structure Observation where
  saved : Int
  marker : Int
  oldAliases : List (Nat × List Int)
  ledger : List (Int × Int)
  caller : Int
  sender : Int
  deriving DecidableEq

def read (σ : State C Γ) : TRes Observation := do
  let saved ← (Val.read (.root "saved" rfl) : Val C Γ .uint).evalT σ
  pure ⟨saved.1, (TEnv.get (.there (.there .here)) σ.env).1,
    aliases σ, σ.net.entries, σ.tx.selfAddress.1, σ.tx.msgSender.1⟩
def execute (p : Prog C [] []) (ws : List Word := words)
    (args : State C Γ → TRes Unit := fun _ => .ok ())
    (ok : (Word × List Word) → TStep C Γ Γ := fun v => (tailBody v.1).run)
    (err : THalt → TStep C Γ Γ := fun _ => (tailBody ⟨18, by decide +kernel⟩).run) :=
  LibraryTryFrame.execute world self initial before.run args (fun _ => raw p ws) ctx decode ok err read

def observe (r : TRes (World catalog × Observation)) := r.map (fun (w, o) =>
  (o, (w.funds (addr 7)).1, (w.funds (addr 10)).1,
    (w.storage? (⟨addr 8⟩ : Handle true)).map (fun (s : Storage C) =>
      ((Val.read (.root "saved" rfl) : Val C [] .uint).evalT (State.ofStorage s)).toOption.map (fun (v : Word) => v.1))))
def reverted (d : List UInt8) : Prog C [] [] := .cons (.revertData [.bytes d]) .nil

theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r <;> first | rfl | cases h

theorem prefix_actual : before.run initial = .ok start ∧
    world.finish (k := false) self.address start.st = .ok pre := by
  constructor
  · unfold start
    exact actual_get _ _
  · unfold pre
    exact actual_get _ _

theorem total_actual : ∀ σ, (raw body).target.entry.result σ = .ok words := fun _ => rfl

/-- Prefix pays 3, selected tail pays 2: neither the prefix nor its incoming
ledger is charged twice. Library storage remains 0 while caller storage is 12. -/
theorem success_actual : (observe (execute body)).toOption =
    some (⟨12, 12, [(0,[161,0,178]),(0,[161,0,178])], [(10,-2)], 7, 9⟩,
      95, 5, some (some 0)) := by decide +kernel

/-- A failed library keeps the actual prefix write 9, payment 3 and live aliases;
then the catch tail alone writes marker 18 and pays 2. -/
theorem caught_actual : (observe (execute (reverted [222,173,0,255]))).toOption =
    some (⟨9, 18, [(0,[161,0,178]),(0,[161,0,178])], [(10,-2)], 7, 9⟩,
      95, 5, some (some 0)) := by decide +kernel

/-- The actual prefix commit preserves catalog roles, independently of ledger contents. -/
theorem finish_roles {w next : World catalog} {Γ : Ctx} (σ : State C Γ)
    (h : w.finish (k := false) self.address σ = .ok next) : next.roles = w.roles := by
  unfold World.finish at h
  cases hs : settle w.funds self.address σ.net with
  | error e => simp only [hs, bind, Except.bind] at h; cases h
  | ok funds => simp only [hs, bind, Except.bind] at h; cases h; rfl

theorem pre_caller : pre.storage? self = some start.st.storage := by
  unfold World.storage?
  rw [World.finish_accounts prefix_actual.2]
  simp only [ite_true, bind, Option.bind, dite_true]

theorem pre_library : pre.storage? (⟨addr 8⟩ : Handle true) = some (State.init C).storage := by
  unfold World.storage?
  rw [World.finish_accounts prefix_actual.2]
  have h : addr 8 ≠ self.address := by decide +kernel
  simp only [if_neg h, world, bind, Option.bind]
  rfl

theorem called_revert (d : List UInt8) :
    pre.libraryCall self (raw (reverted d)).target ctx = .error (THalt.ofData d) := by
  have roles : pre.roles = world.roles := finish_roles start.st prefix_actual.2
  have libRole : pre.isLibrary true = true := by rw [World.isLibrary, roles]; rfl
  have callerRole : pre.isLibrary false = false := by rw [World.isLibrary, roles]; rfl
  rw [LibraryTryFrame.library_frame pre self (raw (reverted d)).target ctx start.st.storage
    (State.init C).storage libRole callerRole rfl pre_library pre_caller]
  simp only [raw, reverted, Prog.run, Prog.runR, TRun.seq, TRun.revertData, RevPart.evalT,
    List.mapM_cons, List.mapM_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    bind, Except.bind, pure, Except.pure]

/-- The uniform theorem is applied with a real populated prefix and real failure. -/
theorem caught_application :
    execute (reverted [222,173,0,255]) =
      tail pre self start.st (tailBody ⟨18, by decide +kernel⟩).run read := by
  exact execute_caught world pre self initial before.run start (fun _ => .ok ()) ()
    (fun _ => raw (reverted [222,173,0,255])) ctx decode _ _ read
    (.revertWith [222,173,0,255]) prefix_actual.1 rfl prefix_actual.2 (called_revert _) rfl

/-- The selected typed continuation transports the full actual halt packet. -/
def caughtPacket (d : List UInt8) : TRes (Observation × List UInt8) :=
  LibraryTryFrame.run pre self (.ok ()) (fun _ => raw (reverted d)) ctx decode
    (fun next v => (tail next self start.st (tailBody v.1).run read).map (fun (_,o) => (o, [])))
    (fun next e => (tail next self start.st (tailBody ⟨18, by decide +kernel⟩).run read).map
      (fun (_,o) => (o, e.data)))

theorem packet_actual (d : List UInt8) : (caughtPacket d).map Prod.snd = .ok d := by
  unfold caughtPacket
  rw [LibraryTryFrame.caught pre self () (fun _ => raw (reverted d)) ctx decode _ _
    (THalt.ofData d) (called_revert d) (by cases d <;> rfl)]
  have h : ∃ w o, tail pre self start.st (tailBody ⟨18, by decide +kernel⟩).run read = .ok (w,o) := by
    have hs : (tail pre self start.st (tailBody ⟨18, by decide +kernel⟩).run read).toOption.isSome = true := by
      rw [← caught_application]
      decide +kernel
    cases hr : tail pre self start.st (tailBody ⟨18, by decide +kernel⟩).run read with
    | error e => rw [hr] at hs; cases hs
    | ok pair => exact ⟨pair.1, pair.2, rfl⟩
  rcases h with ⟨w,o,hr⟩
  rw [hr]
  cases d <;> rfl

/-- Both complete canonical Error bytes and raw custom bytes survive the actual
operation and typed caller continuation; reason catch uses the existing codec. -/
theorem error_packet :
    (caughtPacket (Source.errorData [66,0,254])).map Prod.snd = .ok (Source.errorData [66,0,254]) ∧
    CatchKind.reason.decode (Source.errorData [66,0,254]) = some [66,0,254] := by
  exact ⟨packet_actual _, by rw [PublishedLayout.source_error_bytes]; exact catch_error _ (by decide +kernel)⟩

/-- Actual typed caller programs, rather than stipulated error-valued steps. -/
def failingTail (d : List UInt8) : Prog C Γ Γ := .cons (.revertData [.bytes d]) .nil

theorem argument_failure :
    (execute body words (fun σ => ((failingTail [9,0,8]).run σ).map (fun _ => ()))).halt? =
      some (.revertWith [9,0,8]) := by decide +kernel

theorem decode_failure : (execute body []).halt? = some .revert := by decide +kernel

theorem success_tail_failure :
    (execute body words (fun _ => .ok ()) (fun _ => (failingTail [7,0,8]).run)).halt? =
      some (.revertWith [7,0,8]) := by decide +kernel

theorem catch_tail_failure :
    (execute (reverted [222,173]) words (fun _ => .ok ())
      (fun v => (tailBody v.1).run) (fun _ => (failingTail [1,0,2]).run)).halt? =
      some (.revertWith [1,0,2]) := by decide +kernel

/-- Uniform live-frame transport instantiated at the actual populated caller. -/
theorem live_actual :
    (LibraryTryFrame.resume pre self start.st).map
      (fun τ => (live τ, τ.storage, τ.selfBalance, τ.net)) =
      .ok (live start.st, start.st.storage, pre.funds self.address, []) :=
  resume_live pre self start.st start.st.storage pre_caller

theorem populated_actual : aliases start.st = [(0,[161,0,178]),(0,[161,0,178])] ∧
    start.st.H.length = 1 ∧ (TEnv.get (.there (.there .here)) start.st.env).1 = 77 ∧
    start.st.net.entries = [(10,-3)] := by decide +kernel

/-- The successful operation's full ordered raw result and the published
primitive binder's unconsumed suffix are both retained by this consumer. -/
def successWords : TRes (Observation × Word × List Word) :=
  LibraryTryFrame.run pre self (.ok ()) (fun _ => raw body) ctx decode
    (fun next value => (tail next self start.st (tailBody value.1).run read).map
      (fun (_,o) => (o, value.1, value.2)))
    (fun _ e => .error e)

theorem ordered_result : (successWords.map (fun (_,v,rest) => (v.1, rest.map (fun x => x.1)))).toOption =
    some (12,[0,254]) := by decide +kernel

theorem wrong_order : (successWords.map (fun (_,v,rest) => (v.1, rest.map (fun x => x.1)))).toOption ≠
    some (12,[254,0]) := by rw [ordered_result]; decide +kernel

theorem custom_packet : (caughtPacket [222,173,0,255]).map Prod.snd = .ok [222,173,0,255] :=
  packet_actual _

/-- Direct observations consume the actual returned packet, not a paired
standalone decoder proposition. The complete bytes are fixed by packet_actual. -/
theorem observe_packet {α : Type} (d : List UInt8) (f : List UInt8 → α) :
    (caughtPacket d).map (fun (_,bs) => f bs) = .ok (f d) := by
  have h := packet_actual d
  generalize hr : caughtPacket d = r at h ⊢
  cases r with
  | error e => cases h
  | ok pair =>
    have he : pair.2 = d := Except.ok.inj h
    rw [← he]
    rfl

theorem reason_execution (bs : List UInt8) (hlen : bs.length < 256 ^ 32) :
    (caughtPacket (Source.errorData bs)).map (fun (_,d) => CatchKind.reason.decode d) =
      .ok (some bs) := by
  rw [observe_packet, PublishedLayout.source_error_bytes, catch_error bs hlen]

theorem wrong_catch_class : ((caughtPacket [222,173,0,255]).map
    (fun (_,bs) => CatchKind.reason.decode bs)).toOption = some none := by
  rw [observe_packet]
  rfl

def unpadded : List UInt8 := Semantics.errorSelector ++ Semantics.wordBytes 32 ++
  Semantics.wordBytes 3 ++ [66,0,254]
def truncated : List UInt8 := Semantics.errorSelector ++ Semantics.wordBytes 32 ++
  Semantics.wordBytes 3 ++ [66,0]

theorem accepted_unpadded : (caughtPacket unpadded).map (fun (_,d) => CatchKind.reason.decode d) =
    .ok (some [66,0,254]) := by
  rw [observe_packet]
  apply congrArg Except.ok
  decide +kernel

theorem malformed_packet : (caughtPacket truncated).map (fun (_,d) => CatchKind.reason.decode d) =
    .ok none := by
  rw [observe_packet]
  apply congrArg Except.ok
  decide +kernel

/-- Refusals are the actual installed operation's failures. No source-library
catch guard is weakened to force execution. -/
theorem role_refusal :
    (({ pre with roles := fun _ => .contractCode } : World catalog).libraryCall self
      (raw body).target ctx).halt? = some .revert := by decide +kernel

theorem address_refusal :
    (pre.libraryCall self { (raw body).target with address := addr 99 } ctx).halt? = some .revert := by decide +kernel

theorem static_refusal :
    (pre.libraryCall self (raw body).target { ctx with mode := .readOnly }).halt? = some .revert := by decide +kernel

/-- Outer rollback restores the actual original world, unlike a catch which
keeps the prefix world. This theorem claims no journal/world identification. -/
theorem failed_tail_atomic : atomic world
    (execute body words (fun _ => .ok ()) (fun _ => (failingTail [7,0,8]).run)) =
      (world, .error (.revertWith [7,0,8])) := by
  have h := success_tail_failure
  generalize hr : execute body words (fun _ => .ok ()) (fun _ => (failingTail [7,0,8]).run) = r at h ⊢
  cases r with
  | error e => cases h; rfl
  | ok pair => cases h

/-- Observation-only composition with WorldFrames: the events here are the
actual caught bytes, preceded by explicitly supplied caller observations.
This identifies no Source journal state with a ContractWorld state. -/
theorem packet_prefix_associative (xs ys : List UInt8) (d : List UInt8) :
    (caughtPacket d).map (fun (o,bs) => prependEvents xs
      (prependEvents ys (⟨bs, some o⟩ : Roadmap.Prefix UInt8 Observation))) =
    (caughtPacket d).map (fun (o,bs) => prependEvents (xs ++ ys)
      (⟨bs, some o⟩ : Roadmap.Prefix UInt8 Observation)) := by
  congr 1
  funext pair
  exact prependEvents_assoc xs ys ⟨pair.2, some pair.1⟩


/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.live_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_actual
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.success_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_actual
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.caught_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms caught_application
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.packet_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packet_actual
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.failed_tail_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failed_tail_atomic

/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.reason_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reason_execution
/-- info: 'Solidity.Backend.AbiWorld.LibraryFrameControls.packet_prefix_associative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packet_prefix_associative
end Solidity.Backend.AbiWorld.LibraryFrameControls
