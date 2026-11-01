import Solidity.Backend.MemoryOps.SourceUintDeclaration
import Solidity.Backend.MemoryOps.SourceUintAssignment
import Solidity.Backend.MemoryOps.SourceStructDeclaration

/-! Actual numeric declaration then reached old-object mutation. Source local
cons, intrinsic heap extension and target local offsets are derived separately.
This is composition of existing operations, not a new evaluator or allocator. -/
namespace Solidity.Backend.MemoryOps

def sourceUintDeclareAssign {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index rhs : Source.Idx Γ (.int .u256)) :
    Source.RItems E [] false .body Γ ((.array .memory (.int .u256) none)::Γ) :=
  .stmt (.declVar (.array .memory (.int .u256) none))
    (.stmt (.expr (sourceUintIndexedAssign (.there root) (.there index) (.there rhs))) .nil)

/-- INITIAL alignment and old-object bounds derive the actual successful prefix,
shifted reached mutation, intrinsic program and entire word append. -/
theorem SourceUintMemoryAt.declare_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si sv : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (i v : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hspace : cursor.val+1<Evm.W) (hcap : b+(Δ.length+1)≤frame) :
    let A := RefTy.array (.prim .uint)
    let SA := Source.STy.array .memory (.int .u256) none
    let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
    let σ' := σ.allocPush o
    let e := List.prefix_append σ.H [A]
    let rr := r.wk e
    let fresh := (σ.alloc o).2
    let base' := Evm.upd base σ.H.length cursor
    let mm := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cell (b+Δ.length)) (.val cursor)
    ∃ (mid z : Source.EMState E (SA::Γ)) (out : Heap σ'.H) (target : Evm.Machine),
      (Source.execS G Fsrc (n+5) Γ.length none (.declVar SA : Source.RStmt E [] false .body Γ (SA::Γ)) y.1).run (.nil,y.2)=
        (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execS G Fsrc (n+4) Γ.length none
        (.expr (sourceUintIndexedAssign (.there sroot) (.there si) (.there sv)) : Source.RStmt E [] false .body (SA::Γ) (SA::Γ)) mid.1).run (.nil,mid.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+6) Γ.length none (sourceUintDeclareAssign sroot si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      σ'.heap.writeAddr (.index rr .dyn k) value=some out ∧
      Prog.run σ (.cons (.declMem A (.user "freshUint") none rfl rfl)
        (.cons (.assignMem (.index .dyn (.var (.there root) rfl) (.simple (.local (.there i))))
          (.val (.simple (.local (.there v))))) .nil))=
        .ok ⟨σ'.withHeap out,e⟩ ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint)) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) (Γ := .mem A::Δ) b (.there root) (.simple (.local (.there i))) (.simple (.local (.there v)))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.declareNewCode b (.lit 0 rfl : Simple C Δ .uint) ++
        Evm.Memory.writeLocalCode (C := C) (Γ := .mem A::Δ) b (.there root) (.simple (.local (.there i))) (.simple (.local (.there v)))) m=.ok target 0 ∧
      SourceUintMemoryAt mid address σ'.heap rr .dyn ∧ SourceUintMemoryAt z address out rr .dyn ∧
      SourceUintMemoryAt mid y.2.heap.next σ'.heap fresh .dyn ∧
      out.get fresh=σ'.heap.get fresh ∧
      (∀ q,q≠address → z.2.heap.get q=mid.2.heap.get q) ∧
      Source.MemOK E SH mid ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame (F.push (.mem A) .ok) (σ'.withHeap out) base' target ∧
      Evm.Memory.StructAllocatorRepr out base' frame ⟨cursor.val+1,hspace⟩ target ∧
      mid.2={y.2 with heap := (y.2.heap.alloc ⟨SA,sourceUintMemory []⟩).1} ∧
      mid.1=Source.Locals.cons (.memRef rfl y.2.heap.next) y.1 ∧
      mid.1.get (.there sroot)=.memRef rfl address ∧ mid.1.get .here=.memRef rfl y.2.heap.next ∧
      z.1=mid.1 ∧ target.stack=m.stack := by
  dsimp only
  let A := RefTy.array (.prim .uint)
  let SA := Source.STy.array .memory (.int .u256) none
  let o := Evm.Memory.defaultArray (H := σ.H) .uint ⟨0,Evm.W_pos⟩
  let e := List.prefix_append σ.H [A]
  let σ' := σ.allocPush o
  obtain ⟨z0,hzero,hdecl,hd,hcode,hfresh,hmem',hm',ha',hstack,hid⟩ :=
    source_uint_declaration_word G Fsrc y (n+2) SH hmem σ hm ha hb hspace hcap
  let mid : Source.EMState E (SA::Γ) := (.cons (.memRef rfl y.2.heap.next) z0.1,z0.2)
  have hzid := congrArg Prod.snd (hzero.symm.trans (source_uint_default_run y (n+2)))
  dsimp only at hzid
  have hzlocals : z0.1=y.1 := by rw [hzid]
  have hframe := hr.declaration_frame G Fsrc (n+2)
  rw [hzero] at hframe
  have hrold : SourceUintMemoryAt mid address σ'.heap (r.wk e) .dyn := hframe.2.1
  have hkeep : Heap.Keeps e σ.heap σ'.heap := hframe.2.2.1
  have hsr : mid.1.get (.there sroot)=.memRef rfl address := by change z0.1.get sroot=_;rw [hzlocals];exact hsroot
  have hsi' : mid.1.get (.there si)=sourceUint k := by change z0.1.get si=_;rw [hzlocals];exact hsi
  have hsv' : mid.1.get (.there sv)=sourceUint value := by change z0.1.get sv=_;rw [hzlocals];exact hsv
  have htr : TEnv.get (.there root) σ'.env=some (r.wk e) := by
    change TEnv.get root (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk]
    change (TEnv.get root σ.env).map (HRef.wk e)=_
    rw [htroot];rfl
  have hti' : TEnv.get (.there i) σ'.env=k := by
    change TEnv.get i (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk];exact hti
  have htv' : TEnv.get (.there v) σ'.env=value := by
    change TEnv.get v (TEnv.wk e Δ σ.env)=_
    rw [TEnv.get_wk];exact htv
  have hk' : k.1.toNat<σ'.heap.len (r.wk e) .dyn := by rw [hkeep.len r .dyn];exact hk
  obtain ⟨out,z,target,hw,hswrite,he,hs,hi,hc,hrz,hmz,hmk,hl,hstk,halloc⟩ :=
    resolved_uint_assign_word G Fsrc n σ' (r.wk e) hrold (.there sroot) (.there si) (.there sv)
      (.there root) (.there i) (.there v) k value hsr hsi' hsv' htr hti' htv' hk' hm' SH hmem'
  have hframes := hrold.write_frames Fsrc (n+2) k value hk' hw hswrite
  have hs' := source_expr_statement_run G Fsrc (n+3) Γ.length _ mid z _ he
  have hne : (r.wk e).id≠(σ.alloc o).2.id := by
    change r.id≠σ.H.length
    have h := r.id_lt
    omega
  refine ⟨mid,z,out,target,hdecl,hs',?_,hw,?_,hcode,hc,?_,hrold,hrz,hfresh,
    indexedWrite_frame σ'.heap out (r.wk e) .dyn k value hw (σ.alloc o).2 hne,hframes.2.2.1,hmem',hmk,hmz,
    halloc ⟨cursor.val+1,hspace⟩ hb ha',?_,?_,hsr,rfl,hl,hstk.trans hstack⟩
  · exact source_items_context_pair_run G Fsrc n Γ.length _ _ y mid z hdecl hs'
  · have hd' : Stmt.run σ (.declMem A (.user "freshUint") none rfl rfl)=.ok ⟨σ',e⟩ := hd
    rw [Prog.run_cons_ok hd',Prog.run_cons_ok hi,Prog.run_nil]
    rfl
  · rw [Evm.run_append_ok hcode];exact hc
  · change z0.2=_
    rw [hzid]
  · change Source.Locals.cons _ z0.1=Source.Locals.cons _ y.1
    rw [hzlocals]

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.declare_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.declare_assign_word
end Solidity.Backend.MemoryOps
