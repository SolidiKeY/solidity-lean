import Solidity.Backend.CalldataPackets.RawInt.Execution
namespace Solidity.Backend.CalldataPackets.RawInt.Controls

def int8 : Source.IntTy := ⟨true,8,by decide⟩
def frame (bytes : List UInt8) : Source.Fr :=
  { this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,
    static := false,contract := "RawInt",cd := bytes }

theorem negative_one : (Source.Val.int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-1) (by decide)).word.bind (Source.readInt int8)=some (-1) := by
  exact Source.Val.word_int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-1) (by decide)
theorem positive_max : Source.readInt int8 (Source.toWord 127)=some 127 := by decide
theorem negative_min : (Source.Val.int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-128) (by decide)).word.bind (Source.readInt int8)=some (-128) := by
  exact Source.Val.word_int (D := Source.Env.layout ⟨[]⟩) (t := int8) (-128) (by decide)
theorem dirty_positive : Source.readInt int8 (Source.toWord 128)=none := by decide
theorem dirty_negative : Source.readInt int8 (Source.toWord 255)=none := by decide

theorem dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 255)) (ArrayTy int8) 0 1).run y=
      (.error (.revert []),y) := by
  rw [copy_run]
  rfl

theorem positive_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 127)) (ArrayTy int8) 0 1).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int 127 (by decide)]⟩).1})) := by
  rw [copy_run]
  rfl

theorem late_dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (Source.natBytes 32 127++Source.natBytes 32 255))
      (ArrayTy int8) 0 2).run y=(.error (.revert []),y) := by
  rw [copy_run]
  rfl

theorem empty_copy {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr)
    (off : Nat) (y : Source.EMState E Γ) :
    (Source.cdToMem F (ArrayTy int8) off 0).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨ArrayTy int8,memory []⟩).1})) := by
  rw [copy_run]
  rfl

theorem eof_padding {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame []) (ArrayTy int8) 123 1).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int 0 (by decide)]⟩).1})) := by
  rw [copy_run]
  rfl

theorem zero_horizon {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E)
    (F : Source.Fr) (t : Source.IntTy) (i : Source.Idx Γ (.array .calldata (.int t) none))
    (y : Source.EMState E Γ) :
    (Source.evalE G F 0 (copyExpr t i)).run y=(.error .timeout,y) := rfl

theorem one_horizon {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E)
    (F : Source.Fr) (t : Source.IntTy) (i : Source.Idx Γ (.array .calldata (.int t) none))
    (y : Source.EMState E Γ) :
    (Source.evalE G F 1 (copyExpr t i)).run y=(.error .timeout,y) := rfl

/-! ## Width-specific acceptance at and near every boundary -/

def int16 : Source.IntTy := ⟨true,16,by decide⟩
def int248 : Source.IntTy := ⟨true,248,by decide⟩
def int256 : Source.IntTy := ⟨true,256,by decide⟩
def uint8 : Source.IntTy := ⟨false,8,by decide⟩

theorem int8_near_width :
    accepted int8 127 ∧ ¬accepted int8 128 ∧ accepted int8 (2^256-128) ∧ ¬accepted int8 (2^256-129) := by
  decide
theorem int16_near_width :
    accepted int16 (2^15-1) ∧ ¬accepted int16 (2^15) ∧
      accepted int16 (2^256-2^15) ∧ ¬accepted int16 (2^256-2^15-1) := by
  decide
theorem int248_near_width :
    accepted int248 (2^247-1) ∧ ¬accepted int248 (2^247) ∧
      accepted int248 (2^256-2^247) ∧ ¬accepted int248 (2^256-2^247-1) := by
  decide
/-- At 256 bits every word is a sign extension of itself. -/
theorem int256_all (w : Nat) (hw : w < 2^256) : accepted int256 w := by
  show w < 2^255 ∨ 2^256-2^255 ≤ w
  omega
/-- The same word is clean as `uint8` and dirty as `int8`. -/
theorem sign_matters : accepted uint8 200 ∧ ¬accepted int8 200 := by decide

/-! ## Actual raw negative bytes at mixed offsets

Word values are kernel-checked (`decide +kernel`) facts about the actual bytes;
each element then goes through the actual decoder via `decode_range`. -/

private theorem dec {D : Source.Layout} {t : Source.IntTy} {w : Nat} (v : Int)
    (hv : Source.wordInt t (Source.toWord w)=v) (h : t.lo ≤ v ∧ v ≤ t.hi) :
    Source.decodeWord D w (.int t)=.ok (.int v h) := by
  subst hv
  rw [decode_range,dif_pos h]

private theorem dirty {D : Source.Layout} {t : Source.IntTy} {w : Nat}
    (h : ¬accepted t (Source.toWord w).val) : Source.decodeWord D w (.int t)=.error (.revert []) :=
  decode_dirty D t w h

def negBytes : List UInt8 := [171,205,239]++Source.natBytes 32 (2^256-1)++
  Source.natBytes 32 (2^256-128)++Source.natBytes 32 127

private theorem neg3 : Source.cdWordAt (frame negBytes) 3=2^256-1 := by decide +kernel
private theorem neg35 : Source.cdWordAt (frame negBytes) 35=2^256-128 := by decide +kernel
private theorem neg67 : Source.cdWordAt (frame negBytes) 67=127 := by decide +kernel
private theorem neg2 : Source.cdWordAt (frame negBytes) 2=0xef*256^31+(256^31-1) := by decide +kernel

theorem negative_values {D : Source.Layout} :
    values D int8 (frame negBytes) 3 3=.ok [Source.Val.int (-1) (by decide),
      Source.Val.int (-128) (by decide),Source.Val.int 127 (by decide)] := by
  simp only [values_succ,values_zero,Nat.reduceAdd,neg3,neg35,neg67]
  rw [dec (-1) (by decide +kernel) (by decide),dec (-128) (by decide +kernel) (by decide),
    dec 127 (by decide +kernel) (by decide)]
  rfl


/-- Near-width words through the actual decoder, at both signed boundaries. -/
theorem near_width_decode {D : Source.Layout} :
    Source.decodeWord D (2^256-128) (.int int8)=.ok (.int (-128) (by decide)) ∧
    Source.decodeWord D (2^256-129) (.int int8)=.error (.revert []) ∧
    Source.decodeWord D (2^255) (.int int256)=
      .ok (.int (-((2^255 : Nat) : Int)) (by decide +kernel)) ∧
    Source.decodeWord D (2^255-1) (.int int256)=
      .ok (.int ((2^255-1 : Nat) : Int) (by decide +kernel)) :=
  ⟨dec _ (by decide +kernel) _,dirty (by decide +kernel),dec _ (by decide +kernel) _,
    dec _ (by decide +kernel) _⟩

/-- Three raw words at the unaligned offset 3: `-1`, `-128`, `127`. -/
theorem negative_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame negBytes) (ArrayTy int8) 3 3).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int (-1) (by decide),Source.Val.int (-128) (by decide),
            Source.Val.int 127 (by decide)]⟩).1})) := by
  rw [copy_run,negative_values]

/-- A suffix starting at the second raw word. -/
theorem negative_suffix_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame negBytes) (ArrayTy int8) 35 2).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int (-128) (by decide),Source.Val.int 127 (by decide)]⟩).1})) := by
  have hv : values E.layout int8 (frame negBytes) 35 2=
      .ok [Source.Val.int (-128) (by decide),Source.Val.int 127 (by decide)] := by
    simp only [values_succ,values_zero,Nat.reduceAdd,neg35,neg67]
    rw [dec (-128) (by decide +kernel) (by decide),dec 127 (by decide +kernel) (by decide)]
    rfl
  rw [copy_run,hv]

/-- One byte off: the window `0xef ff…ff` is no sign extension, so the copy reverts. -/
theorem misaligned_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame negBytes) (ArrayTy int8) 2 1).run y=(.error (.revert []),y) := by
  rw [copy_run,values_succ,neg2,dirty (by decide +kernel)]
  rfl

/-- The same negative bytes are dirty for the unsigned type of the same width. -/
theorem unsigned_rejects_negative {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame negBytes) (ArrayTy uint8) 3 1).run y=(.error (.revert []),y) := by
  rw [copy_run,values_succ,neg3,dirty (by decide +kernel)]
  rfl

/-! ## Partial-word padding -/

def padded (b : UInt8) : List UInt8 := Source.natBytes 32 (2^256-1)++[b]

private theorem pad0 (b : UInt8) : Source.cdWordAt (frame (padded b)) 0=2^256-1 := by
  unfold Source.cdWordAt frame padded
  simp only [List.drop_zero]
  rw [show Source.fitBytes 32 (Source.natBytes 32 (2^256-1)++[b])=Source.natBytes 32 (2^256-1) from by
    unfold Source.fitBytes
    rw [List.append_assoc,List.take_left' (by decide)]]
  decide +kernel
private theorem pad255 : Source.cdWordAt (frame (padded 255)) 32=255*256^31 := by decide +kernel
private theorem pad00 : Source.cdWordAt (frame (padded 0)) 32=0 := by decide +kernel

/-- A trailing `0xff` byte pads right to `0xff00…00`: dirty for `int8`, after a clean `-1`. -/
theorem partial_dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (padded 255)) (ArrayTy int8) 0 2).run y=(.error (.revert []),y) := by
  rw [copy_run]
  simp only [values_succ,values_zero,Nat.reduceAdd,pad0,pad255]
  rw [dec (-1) (by decide +kernel) (by decide),dirty (by decide +kernel)]
  rfl

/-- The same padded word is the negative `int256` value `0xff00…00 - 2^256`. -/
theorem partial_int256_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (padded 255)) (ArrayTy int256) 0 2).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int256,memory [Source.Val.int (-1) (by decide +kernel),
            Source.Val.int (((255*256^31 : Nat) : Int)-((2^256 : Nat) : Int)) (by decide +kernel)]⟩).1})) := by
  rw [copy_run]
  simp only [values_succ,values_zero,Nat.reduceAdd,pad0,pad255]
  rw [dec (-1) (by decide +kernel) (by decide +kernel),
    dec (((255*256^31 : Nat) : Int)-((2^256 : Nat) : Int)) (by decide +kernel) (by decide +kernel)]
  rfl

/-- A trailing zero byte pads to the clean zero word. -/
theorem partial_zero_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    (Source.cdToMem (frame (padded 0)) (ArrayTy int8) 0 2).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int (-1) (by decide),Source.Val.int 0 (by decide)]⟩).1})) := by
  rw [copy_run]
  simp only [values_succ,values_zero,Nat.reduceAdd,pad0,pad00]
  rw [dec (-1) (by decide +kernel) (by decide),dec 0 (by decide +kernel) (by decide)]
  rfl

/-! ## Selector and guarded entry under the frame binding -/

def selectorBytes : List UInt8 := [222,173,190,239]
def args : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 (2^256-1)++Source.natBytes 32 5
def dirtyArgs : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 5++Source.natBytes 32 200
def truncated : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++
  Source.natBytes 32 (2^256-1)

private theorem args_entry : Source.wordAt args 0=32 ∧ Source.wordAt (args.drop 32) 0=2 ∧
    args.length=128 := by decide +kernel
private theorem dirty_entry : Source.wordAt dirtyArgs 0=32 ∧ Source.wordAt (dirtyArgs.drop 32) 0=2 ∧
    dirtyArgs.length=128 := by decide +kernel
private theorem truncated_entry : Source.wordAt truncated 0=32 ∧
    Source.wordAt (truncated.drop 32) 0=2 ∧ truncated.length=96 := by decide +kernel
private theorem args68 : Source.cdWordAt (frame (selectorBytes++args)) 68=2^256-1 := by decide +kernel
private theorem args100 : Source.cdWordAt (frame (selectorBytes++args)) 100=5 := by decide +kernel
private theorem dirty68 : Source.cdWordAt (frame (selectorBytes++dirtyArgs)) 68=5 := by decide +kernel
private theorem dirty100 : Source.cdWordAt (frame (selectorBytes++dirtyArgs)) 100=200 := by decide +kernel

/-- Admitted entry: the copied values are the argument bytes after the selector. -/
theorem entry_frame_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail args 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++args)) (ArrayTy int8) p.1 p.2).run y=
      (.ok (.val (.memRef rfl y.2.heap.next)),
        (y.1,{y.2 with heap := (y.2.heap.alloc
          ⟨ArrayTy int8,memory [Source.Val.int (-1) (by decide),Source.Val.int 5 (by decide)]⟩).1})) := by
  rw [guarded_frame_run int8 _ selectorBytes args rfl rfl]
  dsimp only
  rw [args_entry.1,args_entry.2.1,args_entry.2.2,if_neg (by decide),if_neg (by decide),if_pos (by decide),
    ←values_frame E.layout int8 (frame (selectorBytes++args)) selectorBytes args rfl rfl]
  simp only [values_succ,values_zero,Nat.reduceAdd,args68,args100]
  rw [dec (-1) (by decide +kernel) (by decide),dec 5 (by decide +kernel) (by decide)]
  rfl

/-- A dirty second element after admission reverts with the state unchanged. -/
theorem entry_dirty_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail dirtyArgs 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++dirtyArgs)) (ArrayTy int8) p.1 p.2).run y=
      (.error (.revert []),y) := by
  rw [guarded_frame_run int8 _ selectorBytes dirtyArgs rfl rfl]
  dsimp only
  rw [dirty_entry.1,dirty_entry.2.1,dirty_entry.2.2,if_neg (by decide),if_neg (by decide),if_pos (by decide),
    ←values_frame E.layout int8 (frame (selectorBytes++dirtyArgs)) selectorBytes dirtyArgs rfl rfl]
  simp only [values_succ,values_zero,Nat.reduceAdd,dirty68,dirty100]
  rw [dec 5 (by decide +kernel) (by decide),dirty (by decide +kernel)]
  rfl

/-- Truncated elements fail at the entry guard, before any word is read. -/
theorem entry_truncated_copy {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail truncated 0 32)) >>= fun p =>
      Source.cdToMem (frame (selectorBytes++truncated)) (ArrayTy int8) p.1 p.2).run y=
      (.error (.revert []),y) := by
  rw [guarded_frame_run int8 _ selectorBytes truncated rfl rfl]
  dsimp only
  rw [truncated_entry.1,truncated_entry.2.1,truncated_entry.2.2,if_neg (by decide),if_neg (by decide),
    if_neg (by decide)]

end Solidity.Backend.CalldataPackets.RawInt.Controls
