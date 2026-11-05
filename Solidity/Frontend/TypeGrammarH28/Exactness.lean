import Solidity.Frontend.TypeGrammarH28.ParserLengths

/-! All-constructor G09 exactness under explicitly named read-only length-atom
dependencies. These are proof dependencies over original intrinsic Syn; they
are not operational type admission, lowering, or a replacement syntax. -/
namespace Solidity.Frontend.TypeGrammarH28.Exactness
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserCheck ParserPath ParserArray
  ParserContext ParserMapping ParserReady ParserParams ParserFunction ParserLength

inductive Deps : {c : Cat} → Syn c → Prop where
  | elem (e : Elem) : Deps (.elem e)
  | user (p : IdPath) : Deps (.userType p)
  | arrayNone (base : Syn .typeName) (child : Deps base) : Deps (.array base .none)
  | arraySome (base : Syn .typeName) (e : Syn .expr) (child : Deps base) (atom : LengthAtom e) :
      Deps (.array base (.some e))
  | mapping (key : MapKey) (kn : Option String) (value : Syn .typeName) (vn : Option String)
      (child : Deps value) : Deps (.mapping key kn value vn)
  | function (ps : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
      (rs : Syn (.list .param)) (parameters : Deps ps) (returns : Deps rs) :
      Deps (.fnType ps v m rs)
  | param (t : Syn .typeName) (loc : Option DataLoc) (name : Option String) (child : Deps t) :
      Deps (.param t loc name)
  | nil : Deps (Syn.nil (c := .param))
  | cons (p : Syn .param) (ps : Syn (.list .param)) (head : Deps p) (tail : Deps ps) :
      Deps (.cons p ps)

abbrev TypeDeps (t : Syn .typeName) : Prop := Deps t
abbrev ParamDeps (p : Syn .param) : Prop := Deps p
abbrev ParamsDeps (ps : Syn (.list .param)) : Prop := Deps ps

def CertifiedAt {c : Cat} (s : Syn c) : Prop :=
  match c, s with
  | .typeName, t => PrefixCertified t
  | .param, p => ParamCertified p
  | .list .param, ps => ParamsCertified ps
  | _, _ => True

/-- Primitive induction simultaneously discharges every constructor and
parameter/list clause. Each type-name target is actual PrefixCertified. -/
theorem deps_sound {c : Cat} (s : Syn c) (h : Deps s) : CertifiedAt s := by
  induction h with
  | elem e => exact prefix_elem e
  | user p => exact prefix_user p
  | arrayNone base child ih => exact prefix_array_none base ih
  | arraySome base e child atom ih => exact prefix_array_some base e ih atom
  | mapping key kn value vn child ih => exact prefix_mapping value ih key kn vn
  | function ps v m rs parameters returns ihp ihr => exact prefix_fn ps rs v m ihp ihr
  | param t loc name child ih => exact ParserParams.param_certified t ih loc name
  | nil => exact params_nil_certified
  | cons p ps head tail ihp ihr => exact params_cons_certified p ps ihp ihr

/-- Universal constructor closure; only read-only expression atoms are external. -/
theorem type_prefix {t : Syn .typeName} (h : TypeDeps t) : PrefixCertified t := by
  exact deps_sound t h

theorem param_certified {p : Syn .param} (h : ParamDeps p) : ParamCertified p := by
  exact deps_sound p h

theorem params_certified {ps : Syn (.list .param)} (h : ParamsDeps ps) : ParamsCertified ps := by
  exact deps_sound ps h

def ScopedDeps {c : Cat} (s : Syn c) : Prop :=
  match c, s with
  | .typeName, t => TypeDeps t
  | .param, p => ParamDeps p
  | .list .param, ps => ParamsDeps ps
  | _, _ => True

/-- No original constructor/field is filtered: supplying the explicit external
atom dependency for every expression covers every original intrinsic tree. -/
theorem all_constructor_coverage (atoms : ∀ e : Syn .expr, LengthAtom e)
    {c : Cat} (s : Syn c) : ScopedDeps s := by
  induction s <;> try exact True.intro
  case nil d =>
    cases d <;> try exact True.intro
    exact Deps.nil
  case cons d head tail ihh iht =>
    cases d <;> try exact True.intro
    exact Deps.cons head tail ihh iht
  case param t loc name ih => exact Deps.param t loc name ih
  case elem e => exact Deps.elem e
  case fnType ps v m rs ihp ihr => exact Deps.function ps v m rs ihp ihr
  case mapping key kn value vn ih => exact Deps.mapping key kn value vn ih
  case userType p => exact Deps.user p
  case array base len ihb ihl =>
    cases len with
    | none => exact Deps.arrayNone base ihb
    | some e => exact Deps.arraySome base e ihb (atoms e)

/-- Every original tree requires only a finite list of read-only atom facts.
The proof collects array-some payloads; no global expression theorem is assumed. -/
theorem finite_atom_dependencies {c : Cat} (s : Syn c) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) → ScopedDeps s := by
  induction s <;> try exact ⟨[], fun _ => True.intro⟩
  case nil d =>
    cases d <;> try exact ⟨[], fun _ => True.intro⟩
    exact ⟨[], fun _ => Deps.nil⟩
  case cons d head tail ihh iht =>
    cases d <;> try exact ⟨[], fun _ => True.intro⟩
    obtain ⟨ha, hh⟩ := ihh
    obtain ⟨ta, ht⟩ := iht
    exact ⟨ha ++ ta, fun all => Deps.cons head tail
      (hh (fun e he => all e (List.mem_append.mpr (.inl he))))
      (ht (fun e he => all e (List.mem_append.mpr (.inr he))))⟩
  case param t loc name ih =>
    obtain ⟨atoms, ht⟩ := ih
    exact ⟨atoms, fun all => Deps.param t loc name (ht all)⟩
  case elem e => exact ⟨[], fun _ => Deps.elem e⟩
  case fnType ps v m rs ihp ihr =>
    obtain ⟨pa, hp⟩ := ihp
    obtain ⟨ra, hr⟩ := ihr
    exact ⟨pa ++ ra, fun all => Deps.function ps v m rs
      (hp (fun e he => all e (List.mem_append.mpr (.inl he))))
      (hr (fun e he => all e (List.mem_append.mpr (.inr he))))⟩
  case mapping key kn value vn ih =>
    obtain ⟨atoms, ht⟩ := ih
    exact ⟨atoms, fun all => Deps.mapping key kn value vn (ht all)⟩
  case userType p => exact ⟨[], fun _ => Deps.user p⟩
  case array base len ihb ihl =>
    obtain ⟨atoms, ht⟩ := ihb
    cases len with
    | none => exact ⟨atoms, fun all => Deps.arrayNone base (ht all)⟩
    | some e =>
      exact ⟨e :: atoms, fun all => Deps.arraySome base e
        (ht (fun x hx => all x (List.mem_cons_of_mem e hx))) (all e (.head _))⟩

theorem type_certified (t : Syn .typeName) (h : TypeDeps t) : Certified t := by
  exact prefix_to_certified t (type_prefix h)

theorem finite_type_prefix (t : Syn .typeName) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) → PrefixCertified t := by
  obtain ⟨atoms, hc⟩ := finite_atom_dependencies t
  exact ⟨atoms, fun ha => type_prefix (hc ha)⟩

theorem finite_type_completeness (t : Syn .typeName) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) → Certified t := by
  obtain ⟨atoms, hc⟩ := finite_type_prefix t
  exact ⟨atoms, fun ha => prefix_to_certified t (hc ha)⟩

/-- Actual raw parsing at the producer's unchanged token-count fuel. -/
theorem frozen_type_complete (t : Syn .typeName) (h : TypeDeps t)
    (input : List Choice) (tokens : List Tok) (hy : t.toks input = some tokens) (hp : t.prec = true)
    (ls : List Located) (eof : Nat) (hl : ls.map Located.tok = tokens) :
    ∃ layout : List Choice,
      typeName (16 * (ls.length + 1)) ⟨ls, [], eof⟩ = .ok (t, ⟨[], layout.reverse, eof⟩) ∧
      t.toks layout = some tokens := by
  obtain ⟨layout, budget, hr, ht, hb⟩ := type_certified t h input tokens hy hp
  have hlen : ls.length = tokens.length := by
    have he := congrArg List.length hl
    simpa only [List.length_map] using he
  have hf : budget ≤ 16 * (ls.length + 1) := by rw [hlen]; exact hb
  have hc := hr _ hf ls [] hl .eof [] eof
  exact ⟨layout, by simpa only [List.append_nil] using hc, ht⟩

theorem checked_type_complete (t : Syn .typeName) (h : TypeDeps t)
    (input : List Choice) (tokens : List Tok) (hy : t.toks input = some tokens) (hp : t.prec = true)
    (ls : List Located) (eof : Nat) (hl : ls.map Located.tok = tokens) :
    ∃ layout : List Choice, parseCatLocated typeName eof ls = .ok (t, layout) := by
  exact certified_checked t (type_certified t h) input tokens hy hp ls eof hl

/-- Soundness needs no atom/completeness premise. -/
theorem source_type_sound (t : Syn .typeName) (src : Bytes) (h : parseType src = .ok t) :
    ∃ pieces : List Piece, lex src = .ok pieces ∧
      ∃ layout : List Choice, t.toks layout = some (tokensOf pieces) ∧ t.prec = true := by
  obtain ⟨pieces, hl, hd, hp⟩ := parseType_derives h
  obtain ⟨layout, hy⟩ := hd
  exact ⟨pieces, hl, layout, hy, hp⟩

theorem source_type_complete (t : Syn .typeName) (h : TypeDeps t)
    (input : List Choice) (tokens : List Tok) (hy : t.toks input = some tokens) (hp : t.prec = true)
    (src : Bytes) (pieces : List Piece) (hl : lex src = .ok pieces) (ht : tokensOf pieces = tokens) :
    parseType src = .ok t := by
  exact certified_parseType t (type_certified t h) input tokens hy hp src pieces hl ht

theorem source_type_iff (t : Syn .typeName) (h : TypeDeps t) (src : Bytes) :
    parseType src = .ok t ↔ ∃ pieces : List Piece, lex src = .ok pieces ∧
      ∃ layout : List Choice, t.toks layout = some (tokensOf pieces) ∧ t.prec = true := by
  exact certified_parseType_iff t (type_certified t h) src

/-- All-constructor type identity and exact successful layout equivalence.
The original layout witnesses are never equated. -/
theorem type_yield_unique (t u : Syn .typeName) (ht : TypeDeps t) (hu : TypeDeps u)
    (left right : List Choice) (tokens : List Tok)
    (hl : t.toks left = some tokens) (hr : u.toks right = some tokens)
    (hpt : t.prec = true) (hpu : u.prec = true) :
    t = u ∧ LayoutEquivalent t left right := by
  exact certified_yield_unique t u (type_certified t ht) (type_certified u hu) left right tokens hl hr hpt hpu

/-- Every pair of original types has finite explicit atom dependencies for
exactness; this does not assume any final identity or completeness statement. -/
theorem finite_type_exactness (t u : Syn .typeName) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) →
      ∀ left right : List Choice, ∀ tokens : List Tok,
        t.toks left = some tokens → u.toks right = some tokens → t.prec = true → u.prec = true →
        t = u ∧ LayoutEquivalent t left right := by
  obtain ⟨ta, ht⟩ := finite_atom_dependencies t
  obtain ⟨ua, hu⟩ := finite_atom_dependencies u
  refine ⟨ta ++ ua, fun all left right tokens hl hr hpt hpu => ?_⟩
  exact type_yield_unique t u (ht (fun e he => all e (List.mem_append.mpr (.inl he))))
    (hu (fun e he => all e (List.mem_append.mpr (.inr he)))) left right tokens hl hr hpt hpu

theorem finite_source_type_iff (t : Syn .typeName) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) → ∀ src : Bytes,
      (parseType src = .ok t ↔ ∃ pieces : List Piece, lex src = .ok pieces ∧
        ∃ layout : List Choice, t.toks layout = some (tokensOf pieces) ∧ t.prec = true) := by
  obtain ⟨atoms, hc⟩ := finite_atom_dependencies t
  exact ⟨atoms, fun ha src => source_type_iff t (hc ha) src⟩

theorem elem_params_deps (frames : List (Elem × Option DataLoc × Option String)) :
    ParamsDeps (elemParams frames) := by
  induction frames with
  | nil => exact Deps.nil
  | cons frame rest ih =>
    cases frame with
    | mk e pair =>
      cases pair with
      | mk loc name => exact Deps.cons _ _ (Deps.param _ loc name (Deps.elem e)) ih

theorem param_precedence (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (h : t.prec = true) : (Syn.param t loc name).prec = true := by
  have ha : t.all Syn.precNode = true := (Bool.and_eq_true_iff.mp h).2
  change (true && (true && t.all Syn.precNode)) = true
  rw [ha]
  rfl

theorem cons_precedence (p : Syn .param) (ps : Syn (.list .param))
    (hp : p.prec = true) (hs : ps.prec = true) : (Syn.cons p ps).prec = true := by
  have ha := (Bool.and_eq_true_iff.mp hp).2
  have hb := (Bool.and_eq_true_iff.mp hs).2
  change (true && (true && p.all Syn.precNode && ps.all Syn.precNode)) = true
  rw [ha, hb]
  rfl

theorem fn_precedence (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (hp : ps.prec = true) (hr : rs.prec = true) : (Syn.fnType ps v m rs).prec = true := by
  have ha := (Bool.and_eq_true_iff.mp hp).2
  have hb := (Bool.and_eq_true_iff.mp hr).2
  change (true && (true && ps.all Syn.precNode && rs.all Syn.precNode)) = true
  rw [ha, hb]
  rfl

/-- All original field values remain parameters of this inhabited control. -/
structure MixedFields where
  elementary : Elem
  path : IdPath
  key : MapKey
  keyName : Option String
  valueName : Option String
  visibility : Option Visibility
  mutability : Option Mutability
  paramLoc : Option DataLoc
  paramName : Option String
  returnLoc : Option DataLoc
  returnName : Option String
  parameters : List (Elem × Option DataLoc × Option String)
  returns : List (Elem × Option DataLoc × Option String)
  length : NumLit

def mixedParams (f : MixedFields) : Syn (.list .param) :=
  .cons (.param (.array (.elem f.elementary) .none) f.paramLoc f.paramName) (elemParams f.parameters)

def mixedReturns (f : MixedFields) : Syn (.list .param) :=
  .cons (.param (.userType f.path) f.returnLoc f.returnName) (elemParams f.returns)

def mixedType (f : MixedFields) : Syn .typeName :=
  .array (.mapping f.key f.keyName
    (.fnType (mixedParams f) f.visibility f.mutability (mixedReturns f)) f.valueName)
    (.some (.lit (.num f.length)))

/-- Every type constructor, both array branches and all field families occur
in this genuine positive control, without an arbitrary atom assumption. -/
theorem mixed_deps (f : MixedFields) : TypeDeps (mixedType f) := by
  have hp : ParamsDeps (mixedParams f) := Deps.cons _ _
    (Deps.param _ f.paramLoc f.paramName (Deps.arrayNone _ (Deps.elem f.elementary))) (elem_params_deps f.parameters)
  have hr : ParamsDeps (mixedReturns f) := Deps.cons _ _
    (Deps.param _ f.returnLoc f.returnName (Deps.user f.path)) (elem_params_deps f.returns)
  exact Deps.arraySome _ _
    (Deps.mapping f.key f.keyName _ f.valueName (Deps.function _ f.visibility f.mutability _ hp hr))
    (num_length_atom f.length)

theorem mixed_prec (f : MixedFields) : (mixedType f).prec = true := by
  have hp : (mixedParams f).prec = true := cons_precedence _ _
    (param_precedence _ f.paramLoc f.paramName rfl) (elem_params_prec f.parameters)
  have hr : (mixedReturns f).prec = true := cons_precedence _ _
    (param_precedence _ f.returnLoc f.returnName rfl) (elem_params_prec f.returns)
  exact array_some_prec _ _ (mapping_prec _ (fn_precedence _ _ f.visibility f.mutability hp hr)
    f.key f.keyName f.valueName) rfl

theorem mixed_exact (f : MixedFields) :
    ∃ layout : List Choice, ∃ tokens : List Tok, YieldExact (mixedType f) layout [tokens] := by
  let dt := f.elementary.toks ++ pu .lbrack ++ pu .rbrack
  have hd : YieldExact (.array (.elem f.elementary) .none) [] [dt] := by
    have hx := exact_array (.elem f.elementary) .none [] [] [f.elementary.toks] [] (exact_elem f.elementary) exact_no_length
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append] using hx
  have hph := exact_param (.array (.elem f.elementary) .none) f.paramLoc f.paramName [] [dt] hd
  have hph' : YieldExact (.param (.array (.elem f.elementary) .none) f.paramLoc f.paramName) []
      [paramTokens dt f.paramLoc f.paramName] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using hph
  let pi := paramTokens dt f.paramLoc f.paramName :: elemParamItems f.parameters
  have hp : YieldExact (mixedParams f) [] pi := by
    have hx := exact_params_cons _ _ [] [] [paramTokens dt f.paramLoc f.paramName]
      (elemParamItems f.parameters) hph' (elem_params_exact f.parameters)
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append] using hx
  have hrh := exact_param (.userType f.path) f.returnLoc f.returnName [] [f.path.toks] (exact_userType f.path)
  have hrh' : YieldExact (.param (.userType f.path) f.returnLoc f.returnName) []
      [paramTokens f.path.toks f.returnLoc f.returnName] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using hrh
  let ri := paramTokens f.path.toks f.returnLoc f.returnName :: elemParamItems f.returns
  have hr : YieldExact (mixedReturns f) [] ri := by
    have hx := exact_params_cons _ _ [] [] [paramTokens f.path.toks f.returnLoc f.returnName]
      (elemParamItems f.returns) hrh' (elem_params_exact f.returns)
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append] using hx
  obtain ⟨order, attrs, ha, _⟩ := ParserFnAttrs.attrs_inhabited f.visibility f.mutability
  let ft := fnTokens pi attrs ri
  have hf : YieldExact (.fnType (mixedParams f) f.visibility f.mutability (mixedReturns f)) [.attrs order] [ft] :=
    exact_fnType _ _ f.visibility f.mutability order [] [] pi ri attrs hp hr ha
  let mt := mappingTokens f.key f.keyName ft f.valueName
  have hm : YieldExact (.mapping f.key f.keyName
      (.fnType (mixedParams f) f.visibility f.mutability (mixedReturns f)) f.valueName) [.attrs order] [mt] := by
    have hx := exact_mapping f.key f.keyName f.valueName _ [.attrs order] [ft] hf
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hx
  have hs : YieldExact (.some (.lit (.num f.length))) [] [[.num f.length]] := by
    have hx := exact_some_length (.lit (.num f.length)) [] [[.num f.length]] (fun suffix => rfl)
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hx
  have hx := exact_array _ (.some (.lit (.num f.length))) [.attrs order] [] [mt] [[.num f.length]] hm hs
  have he : YieldExact (mixedType f) [.attrs order] [staticTokens mt [.num f.length]] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hx
  exact ⟨[.attrs order], staticTokens mt [.num f.length], he⟩

theorem mixed_checked (f : MixedFields) :
    ∃ layout : List Choice, ∃ tokens : List Tok, ∃ parsed : List Choice,
      (mixedType f).toks layout = some tokens ∧
      parseCatLocated typeName 0 (witnessLocations tokens) = .ok (mixedType f, parsed) := by
  obtain ⟨layout, tokens, hx⟩ := mixed_exact f
  have ht : (mixedType f).toks layout = some tokens := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_toks _ _ _ hx
  obtain ⟨parsed, hp⟩ := checked_type_complete _ (mixed_deps f) layout tokens ht (mixed_prec f)
    (witnessLocations tokens) 0 (witness_locations_tokens tokens)
  exact ⟨layout, tokens, parsed, ht, hp⟩

theorem mixed_source_iff (f : MixedFields) (src : Bytes) :
    parseType src = .ok (mixedType f) ↔ ∃ pieces : List Piece, lex src = .ok pieces ∧
      ∃ layout : List Choice, (mixedType f).toks layout = some (tokensOf pieces) ∧ (mixedType f).prec = true := by
  exact source_type_iff _ (mixed_deps f) src

theorem atom_length_balance (e : Syn .expr) (h : LengthAtom e) (hp : e.prec = true) :
    TypeRegion.LengthBalance (.some e) := by
  apply TypeRegion.some_length_balance e
  intro input chunks remaining hy
  obtain ⟨layout, budget, hpos, hexpr, hprint, hbudget, hbal, hn⟩ := h input chunks remaining hy hp
  exact hbal

def BalancedAt {c : Cat} (s : Syn c) : Prop :=
  match c, s with
  | .typeName, t => t.prec = true → TypeRegion.TypeAtomsBalanced t
  | .param, p => p.prec = true → TypeRegion.ParamAtomsBalanced p
  | .list .param, ps => ps.prec = true → TypeRegion.ParamsAtomsBalanced ps
  | _, _ => True

/-- The same local atom facts discharge all delimiter-balance dependencies;
no separate whole-expression balance or final exactness is assumed. -/
theorem deps_balanced {c : Cat} (s : Syn c) (h : Deps s) : BalancedAt s := by
  induction h with
  | elem e => exact fun _ => .elem e
  | user p => exact fun _ => .userType p
  | arrayNone base child ih =>
    exact fun hp => .array base .none (ih (ParserDynamicClosure.array_none_prec_converse base hp)) TypeRegion.no_length_balance
  | arraySome base e child atom ih =>
    intro hp
    obtain ⟨hb, he⟩ := array_some_prec_converse base e hp
    exact .array base (.some e) (ih hb) (atom_length_balance e atom he)
  | mapping key kn value vn child ih =>
    exact fun hp => .mapping key kn value vn (ih (mapping_prec_converse value key kn vn hp))
  | function ps v m rs parameters returns ihp ihr =>
    intro hp
    obtain ⟨hps, hrs⟩ := fn_prec_converse ps rs v m hp
    exact .fnType ps v m rs (ihp hps) (ihr hrs)
  | param t loc name child ih =>
    exact fun hp => .param t loc name (ih (param_prec_converse t loc name hp))
  | nil => exact fun _ => .nil
  | cons p ps head tail ihp ihr =>
    intro hp
    obtain ⟨hh, ht⟩ := params_cons_prec p ps hp
    exact .cons p ps (ihp hh) (ihr ht)

theorem type_atoms_balanced (t : Syn .typeName) (h : TypeDeps t) (hp : t.prec = true) :
    TypeRegion.TypeAtomsBalanced t := by
  exact deps_balanced t h hp

theorem type_boundary_decomposition (t : Syn .typeName) (h : TypeDeps t) (hp : t.prec = true)
    (layout : List Choice) (tokens suffix : List Tok) (hy : t.toks layout = some tokens)
    (hs : Boundary.StartsBoundary TypeRegion.typeStop suffix) :
    Boundary.cut TypeRegion.typeStop [] (tokens ++ suffix) = some (tokens, suffix) := by
  exact TypeRegion.type_toks_boundary t (type_atoms_balanced t h hp) layout tokens suffix hy hs

/-- Arbitrary-depth decomposition and type identity in one all-constructor
statement, with exact layout equivalence rather than layout witness equality. -/
theorem type_boundary_exactness (t u : Syn .typeName) (ht : TypeDeps t) (hu : TypeDeps u)
    (hpt : t.prec = true) (hpu : u.prec = true) (left right : List Choice)
    (lt rt ls rs : List Tok) (hyl : t.toks left = some lt) (hyr : u.toks right = some rt)
    (hsl : Boundary.StartsBoundary TypeRegion.typeStop ls) (hsr : Boundary.StartsBoundary TypeRegion.typeStop rs)
    (same : lt ++ ls = rt ++ rs) :
    lt = rt ∧ ls = rs ∧ t = u ∧ LayoutEquivalent t left right := by
  obtain ⟨hTokens, hRest⟩ := TypeRegion.type_token_boundary_unique t u
    (type_atoms_balanced t ht hpt) (type_atoms_balanced u hu hpu) left right lt rt ls rs hyl hyr hsl hsr same
  have hr : u.toks right = some lt := by rw [hTokens]; exact hyr
  obtain ⟨hType, hLayout⟩ := type_yield_unique t u ht hu left right lt hyl hr hpt hpu
  exact ⟨hTokens, hRest, hType, hLayout⟩

theorem finite_boundary_exactness (t u : Syn .typeName) :
    ∃ atoms : List (Syn .expr), (∀ e ∈ atoms, LengthAtom e) →
      ∀ left right : List Choice, ∀ lt rt ls rs : List Tok,
        t.prec = true → u.prec = true → t.toks left = some lt → u.toks right = some rt →
        Boundary.StartsBoundary TypeRegion.typeStop ls → Boundary.StartsBoundary TypeRegion.typeStop rs →
        lt ++ ls = rt ++ rs → lt = rt ∧ ls = rs ∧ t = u ∧ LayoutEquivalent t left right := by
  obtain ⟨ta, ht⟩ := finite_atom_dependencies t
  obtain ⟨ua, hu⟩ := finite_atom_dependencies u
  refine ⟨ta ++ ua, fun all left right lt rt ls rs hpt hpu hyl hyr hsl hsr same => ?_⟩
  exact type_boundary_exactness t u (ht (fun e he => all e (List.mem_append.mpr (.inl he))))
    (hu (fun e he => all e (List.mem_append.mpr (.inr he)))) hpt hpu left right lt rt ls rs hyl hyr hsl hsr same

#print axioms deps_sound
#print axioms type_prefix
#print axioms param_certified
#print axioms params_certified
#print axioms all_constructor_coverage
#print axioms finite_atom_dependencies
#print axioms type_certified
#print axioms finite_type_prefix
#print axioms finite_type_completeness
#print axioms frozen_type_complete
#print axioms checked_type_complete
#print axioms source_type_sound
#print axioms source_type_complete
#print axioms source_type_iff
#print axioms type_yield_unique
#print axioms finite_type_exactness
#print axioms finite_source_type_iff
#print axioms elem_params_deps
#print axioms param_precedence
#print axioms cons_precedence
#print axioms fn_precedence
#print axioms mixed_deps
#print axioms mixed_prec
#print axioms mixed_exact
#print axioms mixed_checked
#print axioms mixed_source_iff
#print axioms atom_length_balance
#print axioms deps_balanced
#print axioms type_atoms_balanced
#print axioms type_boundary_decomposition
#print axioms type_boundary_exactness
#print axioms finite_boundary_exactness
end Solidity.Frontend.TypeGrammarH28.Exactness
