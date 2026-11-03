import Solidity.Yul.LocalScope

/-! Whole-group function tables with intrinsic arity references. Preparation
for the block checker; header/body agreement and freshness are its obligations. -/
namespace Solidity.Yul

abbrev FunctionRef (F : List Sig) := (s : Sig) × Member F s

abbrev FunctionNames (F : List Sig) := List (String × FunctionRef F)

/-- Weaken a newly hoisted function reference over older function declarations. -/
def Member.append (post : List Sig) {F : List Sig} {s : Sig} (i : Member F s) :
    Member (F ++ post) s :=
  Member.casesOn (motive := fun F s _ => Member (F ++ post) s) i
    (here := .here)
    (there := fun j => .there (j.append post))
termination_by structural i

/-- Older functions move past the whole new group, preserving their arities. -/
def Member.prefix (pre : List Sig) {F : List Sig} {s : Sig} (i : Member F s) :
    Member (pre ++ F) s :=
  match pre with
  | [] => i
  | _ :: rest => .there (i.prefix rest)

def consFunctionRef (sig : Sig) {F : List Sig} (p : FunctionRef F) : FunctionRef (sig :: F) :=
  ⟨p.1, .there p.2⟩

def appendFunctionRef (post : List Sig) {F : List Sig} (p : FunctionRef F) : FunctionRef (F ++ post) :=
  ⟨p.1, p.2.append post⟩

def prefixFunctionRef (pre : List Sig) {F : List Sig} (p : FunctionRef F) : FunctionRef (pre ++ F) :=
  ⟨p.1, p.2.prefix pre⟩

/-- Build the table from the complete collected header list. The block
collector and its validity certificate remain separate obligations. -/
def groupNames : (headers : List (String × Sig)) → FunctionNames (headers.map Prod.snd)
  | [] => []
  | (name, sig) :: rest =>
    (name, ⟨sig, .here⟩) :: (groupNames rest).map
      (fun p => (p.1, consFunctionRef sig p.2))

/-- Independent source-order declaration membership, retaining exact signature. -/
inductive NamedFunction : (headers : List (String × Sig)) →
    {s : Sig} → Member (headers.map Prod.snd) s → String → Prop where
  | head {name sig rest} : NamedFunction ((name, sig) :: rest) .here name
  | tail {other sig rest s i name} : NamedFunction rest (s := s) i name →
      NamedFunction ((other, sig) :: rest) (.there i) name

theorem NamedFunction.mem {headers s i name} (d : NamedFunction headers (s := s) i name) :
    name ∈ headers.map Prod.fst := by
  induction d with
  | head => exact List.mem_cons_self
  | tail _ ih => exact List.mem_cons_of_mem _ ih

theorem groupNames_sound {headers : List (String × Sig)} {name : String}
    {s : Sig} {i : Member (headers.map Prod.snd) s}
    (h : resolve (groupNames headers) name = some ⟨s, i⟩) : NamedFunction headers i name := by
  induction headers with
  | nil => cases h
  | cons p rest ih =>
      rcases p with ⟨key, sig⟩
      change (if name = key then some (⟨sig, .here⟩ : FunctionRef (sig :: rest.map Prod.snd)) else
        resolve ((groupNames rest).map (fun p => (p.1, consFunctionRef sig p.2))) name) = some ⟨s, i⟩ at h
      split at h
      · next he => subst name; cases h; exact .head
      · rw [resolve_map] at h
        rcases Option.map_eq_some_iff.mp h with ⟨⟨s', j⟩, hj, he⟩
        cases he
        exact .tail (ih hj)

theorem NamedFunction.complete {headers s i name}
    (d : NamedFunction headers (s := s) i name) :
    (headers.map Prod.fst).Nodup → resolve (groupNames headers) name = some ⟨s, i⟩ := by
  induction d with
  | head => intro _; exact if_pos rfl
  | @tail other sig rest s i name d ih =>
      intro hn
      have hs := List.nodup_cons.mp hn
      have hne : name ≠ other := by intro he; exact hs.1 (he ▸ d.mem)
      change (if name = other then some (⟨sig, .here⟩ : FunctionRef (sig :: rest.map Prod.snd)) else
        resolve ((groupNames rest).map (fun p => (p.1, consFunctionRef sig p.2))) name) = _
      rw [if_neg hne, resolve_map, ih hs.2]
      rfl

/-- Extend the whole lexical function environment, with new declarations first. -/
def hoistNames {F : List Sig} (headers : List (String × Sig)) (older : FunctionNames F) :
    FunctionNames (headers.map Prod.snd ++ F) :=
  (groupNames headers).map (fun p => (p.1, appendFunctionRef F p.2)) ++
    older.map (fun p => (p.1, prefixFunctionRef (headers.map Prod.snd) p.2))

theorem hoistNames_new {F : List Sig} {headers : List (String × Sig)}
    {s : Sig} {i : Member (headers.map Prod.snd) s} {name : String}
    (older : FunctionNames F) (hn : (headers.map Prod.fst).Nodup)
    (d : NamedFunction headers i name) :
    resolve (hoistNames headers older) name = some ⟨s, i.append F⟩ := by
  apply resolve_append_some
  rw [resolve_map, d.complete hn]
  rfl

theorem hoistNames_old {F : List Sig} {headers : List (String × Sig)}
    {s : Sig} {i : Member F s} {name : String} {older : FunctionNames F}
    (hn : name ∉ headers.map Prod.fst) (h : resolve older name = some ⟨s, i⟩) :
    resolve (hoistNames headers older) name = some ⟨s, i.prefix (headers.map Prod.snd)⟩ := by
  have hl : resolve (groupNames headers) name = none := by
    apply resolve_none_complete
    rintro ⟨⟨sig, j⟩, d⟩
    exact hn (groupNames_sound (resolve_complete d)).mem
  change resolve (_ ++ _) name = _
  rw [resolve_append_none (by rw [resolve_map, hl]; rfl), resolve_map, h]
  rfl

end Solidity.Yul
