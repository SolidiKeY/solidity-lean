import Solidity.Frontend.TypeGrammarH28.Composition
import Solidity.Frontend.TypeGrammarH28.Boundaries

/-! Actual type-yield token regions. Length atoms enter through independent
balanced-token contracts. No expression identity or final type uniqueness
premise is used by these composition lemmas. -/
namespace Solidity.Frontend.TypeGrammarH28.TypeRegion
open Solidity.Source Solidity.Frontend.Checked Boundary

theorem elem_region (e : Elem) : Region paramStop e.toks := by
  cases e <;> first
    | exact .atom _ _ rfl rfl .nil
    | exact .atom _ _ rfl rfl (.atom _ _ rfl rfl .nil)

theorem path_tail_region (names : List String) :
    Region paramStop (names.flatMap fun s => [.punct .period, .ident s]) := by
  induction names with
  | nil => exact .nil
  | cons name rest ih => exact .atom _ _ rfl rfl (.atom _ _ rfl rfl ih)

theorem path_region (p : IdPath) : Region paramStop p.toks := by
  exact .atom _ _ rfl rfl (path_tail_region p.tail)

theorem name_region (name : Option String) : Region paramStop (optToks idt name) := by
  cases name with
  | none => exact .nil
  | some name => exact .atom _ _ rfl rfl .nil

theorem loc_region (loc : Option DataLoc) : Region paramStop (optToks DataLoc.toks loc) := by
  cases loc with
  | none => exact .nil
  | some loc => cases loc <;> exact .atom _ _ rfl rfl .nil

theorem vis_region (vis : Option Visibility) : Region paramStop (optToks Visibility.toks vis) := by
  cases vis with
  | none => exact .nil
  | some vis => cases vis <;> exact .atom _ _ rfl rfl .nil

theorem mut_region (mu : Option Mutability) : Region paramStop (optToks Mutability.toks mu) := by
  cases mu with
  | none => exact .nil
  | some mu => cases mu <;> exact .atom _ _ rfl rfl .nil

/-- The mapping key spelling is exactly the producer's inline key clause. -/
def keyTokens : MapKey → List Tok
  | .elem e _ => e.toks
  | .path p => p.toks

theorem key_region (key : MapKey) : Region paramStop (keyTokens key) := by
  cases key with
  | elem e h => exact elem_region e
  | path p => exact path_region p

theorem parens_region (ts : List Tok) (h : Balanced ts) : Region paramStop (parens ts) := by
  exact .group .paren ts [] rfl h .nil

theorem brackets_region (ts : List Tok) (h : Balanced ts) :
    Region paramStop (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact .group .bracket ts [] rfl h .nil

/-- Every comma is inside the caller's parentheses; all list lengths supported. -/
theorem commaSep_balanced (items : List (List Tok)) :
    (∀ item ∈ items, Balanced item) → Balanced (commaSep items) := by
  induction items with
  | nil => intro h; exact .nil
  | cons item rest ih =>
    intro h
    have hi : Balanced item := h item List.mem_cons_self
    have hr : ∀ a ∈ rest, Balanced a := fun a ha => h a (List.mem_cons_of_mem item ha)
    cases rest with
    | nil =>
      change Balanced (item ++ [])
      rw [List.append_nil]
      exact hi
    | cons next tail =>
      change Balanced (item ++ (pu .comma ++ commaSep (next :: tail)))
      exact balanced_append _ _ hi
        (balanced_append _ _ (.atom _ _ rfl .nil) (ih hr))

theorem param_region (typeTokens : List Tok) (loc : Option DataLoc) (name : Option String)
    (h : Region paramStop typeTokens) :
    Region paramStop (typeTokens ++ optToks DataLoc.toks loc ++ optToks idt name) := by
  exact region_append _ _ _ (region_append _ _ _ h (loc_region loc)) (name_region name)

/-- The sole expression dependency is balanced length-atom tokens. -/
theorem array_region (base length : List Tok) (hb : Region paramStop base)
    (hl : Balanced length) :
    Region paramStop (base ++ pu .lbrack ++ length ++ pu .rbrack) := by
  have h : Region paramStop (base ++ (pu .lbrack ++ length ++ pu .rbrack)) :=
    region_append _ _ _ hb (brackets_region length hl)
  simpa only [List.append_assoc] using h

theorem mapping_region (key : MapKey) (kn vn : Option String) (value : List Tok)
    (hv : Region paramStop value) :
    Region paramStop (tk .mapping ++ parens
      (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ value ++ optToks idt vn)) := by
  have hi : Region paramStop
      (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ value ++ optToks idt vn) :=
    region_append _ _ _ (region_append _ _ _
      (region_append _ _ _ (region_append _ _ _ (key_region key) (name_region kn))
        (.atom _ _ rfl rfl .nil)) hv) (name_region vn)
  exact .atom _ _ rfl rfl (parens_region _ (region_balanced _ _ hi))

/-- The no-modifier equation, exposed without changing the producer. -/
theorem arrange_cons_nil (slot : Slot) (order : List Slot)
    (singles : List (Slot × List Tok)) :
    arrange (slot :: order) singles [] =
      if slot == .modInv then none else
      match singles.find? (fun p => p.1 == slot) with
      | some (_, ts) => (arrange order (singles.filter (fun p => p.1 != slot)) []).map (ts ++ ·)
      | none => none := by
  cases slot <;> rfl

/-- Successful attribute arrangements preserve region membership of every
present singleton. This is an independent producer helper, not uniqueness. -/
theorem arrange_region (order : List Slot) (singles : List (Slot × List Tok))
    (attrs : List Tok) (h : arrange order singles [] = some attrs)
    (hs : ∀ p ∈ singles, Region paramStop p.2) : Region paramStop attrs := by
  induction order generalizing singles attrs with
  | nil =>
    cases singles with
    | nil =>
      have he : ([] : List Tok) = attrs := Option.some.inj h
      cases he
      exact .nil
    | cons p ps => cases h
  | cons slot order ih =>
    rw [arrange_cons_nil] at h
    split at h
    · cases h
    · cases hf : singles.find? (fun p => p.1 == slot) with
      | none => rw [hf] at h; cases h
      | some p =>
        obtain ⟨selected, ts⟩ := p
        rw [hf] at h
        have hp : Region paramStop ts := hs (selected, ts) (List.mem_of_find?_eq_some hf)
        cases hr : arrange order (singles.filter (fun p => p.1 != slot)) [] with
        | none => rw [hr] at h; cases h
        | some rest =>
          rw [hr] at h
          have he : ts ++ rest = attrs := Option.some.inj h
          have ht : ∀ p ∈ singles.filter (fun p => p.1 != slot), Region paramStop p.2 :=
            fun p hm => hs p (List.mem_filter.mp hm).1
          have hrest : Region paramStop rest := ih _ _ hr ht
          rw [← he]
          exact region_append _ _ _ hp hrest

theorem single_region (slot : Slot) (ts : List Tok) (h : Region paramStop ts) :
    ∀ p ∈ single slot ts, Region paramStop p.2 := by
  intro p hp
  unfold single at hp
  split at hp
  · cases hp
  · cases hp with
    | head => exact h
    | tail _ hn => cases hn

theorem fn_attrs_region (vis : Option Visibility) (mu : Option Mutability)
    (order : List Slot) (attrs : List Tok)
    (h : arrange order (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] = some attrs) :
    Region paramStop attrs := by
  apply arrange_region order _ attrs h
  intro p hp
  obtain hv | hm := List.mem_append.mp hp
  · exact single_region .vis _ (vis_region vis) p hv
  · exact single_region .mutab _ (mut_region mu) p hm

/-- All parameter/return lengths and every successful attribute layout. -/
theorem function_region (ps rs : List (List Tok)) (vis : Option Visibility)
    (mu : Option Mutability) (order : List Slot) (attrs : List Tok)
    (hp : ∀ item ∈ ps, Region paramStop item)
    (hr : ∀ item ∈ rs, Region paramStop item)
    (ha : arrange order (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] = some attrs) :
    Region paramStop (tk .function ++ parens (commaSep ps) ++ attrs ++
      (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs))) := by
  have hps : Balanced (commaSep ps) :=
    commaSep_balanced ps (fun item hi => region_balanced _ _ (hp item hi))
  have hf : Region paramStop (tk .function ++ parens (commaSep ps)) :=
    .atom _ _ rfl rfl (parens_region _ hps)
  have hrets : Region paramStop
      (if rs.isEmpty then [] else tk .returns ++ parens (commaSep rs)) := by
    cases rs with
    | nil => exact .nil
    | cons item rest =>
      exact .atom _ _ rfl rfl (parens_region _
        (commaSep_balanced _ (fun item hi => region_balanced _ _ (hr item hi))))
  exact region_append _ _ _ (region_append _ _ _ hf (fn_attrs_region vis mu order attrs ha)) hrets

/-- Independent balance of an optional length atom's actual token yield.
It says nothing about expression identity, evaluation or parser behavior. -/
def LengthBalance (len : Syn (.opt .expr)) : Prop :=
  ∀ input items rest, len.yield input = some (items, rest) → Balanced items.flatten

mutual
/-- Exactly the same local length obligations, represented as a proof
certificate so the yield theorem can recurse structurally on the certificate. -/
inductive TypeAtomsBalanced : Syn .typeName → Prop where
  | elem (e : Elem) : TypeAtomsBalanced (.elem e)
  | userType (p : IdPath) : TypeAtomsBalanced (.userType p)
  | array (t : Syn .typeName) (len : Syn (.opt .expr)) :
      TypeAtomsBalanced t → LengthBalance len → TypeAtomsBalanced (.array t len)
  | mapping (key : MapKey) (kn : Option String) (v : Syn .typeName) (vn : Option String) :
      TypeAtomsBalanced v → TypeAtomsBalanced (.mapping key kn v vn)
  | fnType (ps : Syn (.list .param)) (vis : Option Visibility) (mu : Option Mutability)
      (rs : Syn (.list .param)) :
      ParamsAtomsBalanced ps → ParamsAtomsBalanced rs → TypeAtomsBalanced (.fnType ps vis mu rs)

inductive ParamAtomsBalanced : Syn .param → Prop where
  | param (t : Syn .typeName) (loc : Option DataLoc) (name : Option String) :
      TypeAtomsBalanced t → ParamAtomsBalanced (.param t loc name)

inductive ParamsAtomsBalanced : Syn (.list .param) → Prop where
  | nil : ParamsAtomsBalanced .nil
  | cons (p : Syn .param) (ps : Syn (.list .param)) :
      ParamAtomsBalanced p → ParamsAtomsBalanced ps → ParamsAtomsBalanced (.cons p ps)
end

/-- Constructor clauses are equivalent to the original recursive obligations. -/
theorem atoms_elem_iff (e : Elem) : TypeAtomsBalanced (.elem e) ↔ True := by
  exact ⟨fun _ => True.intro, fun _ => .elem e⟩

theorem atoms_userType_iff (p : IdPath) : TypeAtomsBalanced (.userType p) ↔ True := by
  exact ⟨fun _ => True.intro, fun _ => .userType p⟩

theorem atoms_array_iff (t : Syn .typeName) (len : Syn (.opt .expr)) :
    TypeAtomsBalanced (.array t len) ↔ TypeAtomsBalanced t ∧ LengthBalance len := by
  constructor
  · intro h
    cases h with
    | array _ _ ht hl => exact ⟨ht, hl⟩
  · intro h
    exact .array t len h.1 h.2

theorem atoms_mapping_iff (key : MapKey) (kn : Option String) (v : Syn .typeName)
    (vn : Option String) : TypeAtomsBalanced (.mapping key kn v vn) ↔ TypeAtomsBalanced v := by
  constructor
  · intro h
    cases h with
    | mapping _ _ _ _ hv => exact hv
  · intro h
    exact .mapping key kn v vn h

theorem atoms_fnType_iff (ps rs : Syn (.list .param)) (vis : Option Visibility)
    (mu : Option Mutability) :
    TypeAtomsBalanced (.fnType ps vis mu rs) ↔ ParamsAtomsBalanced ps ∧ ParamsAtomsBalanced rs := by
  constructor
  · intro h
    cases h with
    | fnType _ _ _ _ hp hr => exact ⟨hp, hr⟩
  · intro h
    exact .fnType ps vis mu rs h.1 h.2

theorem atoms_param_iff (t : Syn .typeName) (loc : Option DataLoc) (name : Option String) :
    ParamAtomsBalanced (.param t loc name) ↔ TypeAtomsBalanced t := by
  constructor
  · intro h
    cases h with
    | param _ _ _ ht => exact ht
  · intro h
    exact .param t loc name h

theorem atoms_params_nil_iff : ParamsAtomsBalanced .nil ↔ True := by
  exact ⟨fun _ => True.intro, fun _ => .nil⟩

theorem atoms_params_cons_iff (p : Syn .param) (ps : Syn (.list .param)) :
    ParamsAtomsBalanced (.cons p ps) ↔ ParamAtomsBalanced p ∧ ParamsAtomsBalanced ps := by
  constructor
  · intro h
    cases h with
    | cons _ _ hp hs => exact ⟨hp, hs⟩
  · intro h
    exact .cons p ps h.1 h.2

theorem no_length_balance : LengthBalance .none := by
  intro input items rest h
  have he : (([] : List (List Tok)), input) = (items, rest) := Option.some.inj h
  cases he
  exact .nil

theorem some_length_balance (e : Syn .expr)
    (ha : ∀ input items rest, e.yield input = some (items, rest) → Balanced items.flatten) :
    LengthBalance (.some e) := by
  intro input items rest h
  change (e.yield input >>= fun p => some ([p.1.flatten], p.2)) = some (items, rest) at h
  cases he : e.yield input with
  | none => rw [he] at h; cases h
  | some p =>
    obtain ⟨a, last⟩ := p
    rw [he] at h
    have hh : ([a.flatten], last) = (items, rest) := Option.some.inj h
    cases hh
    change Balanced (a.flatten ++ [])
    rw [List.append_nil]
    exact ha input a rest he

/-- Inhabited static atoms include every numeric literal, without evaluation. -/
theorem numeric_length_balance (n : NumLit) : LengthBalance (.some (.lit (.num n))) := by
  apply some_length_balance
  intro input items rest h
  have he : ([[Tok.num n]], input) = (items, rest) := Option.some.inj h
  cases he
  exact .atom _ _ rfl .nil

/-- The mutual induction motives retain the actual producer yield. -/
def TypeYieldRegion (t : Syn .typeName) : Prop :=
  ∀ (input : List Choice) (items : List (List Tok)) (rest : List Choice),
    t.yield input = some (items, rest) → Region paramStop items.flatten

def ParamYieldRegion (p : Syn .param) : Prop :=
  ∀ (input : List Choice) (items : List (List Tok)) (rest : List Choice),
    p.yield input = some (items, rest) → Region paramStop items.flatten

def ParamsYieldRegions (ps : Syn (.list .param)) : Prop :=
  ∀ (input : List Choice) (items : List (List Tok)) (rest : List Choice),
    ps.yield input = some (items, rest) → ∀ item ∈ items, Region paramStop item

theorem yield_elem_region (e : Elem) : TypeYieldRegion (.elem e) := by
  intro input items rest hy
  have he : ([e.toks], input) = (items, rest) := Option.some.inj hy
  cases he
  change Region paramStop (e.toks ++ [])
  rw [List.append_nil]
  exact elem_region e

theorem yield_userType_region (p : IdPath) : TypeYieldRegion (.userType p) := by
  intro input items rest hy
  have he : ([p.toks], input) = (items, rest) := Option.some.inj hy
  cases he
  change Region paramStop (p.toks ++ [])
  rw [List.append_nil]
  exact path_region p

theorem yield_mapping_region (key : MapKey) (kn : Option String) (value : Syn .typeName) (vn : Option String)
    (hvalue : TypeYieldRegion value) : TypeYieldRegion (.mapping key kn value vn) := by
  intro input items rest hy
  change (value.yield input >>= fun p => some ([tk .mapping ++ parens
    (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ p.1.flatten ++ optToks idt vn)], p.2)) =
      some (items, rest) at hy
  cases hv : value.yield input with
  | none => rw [hv] at hy; cases hy
  | some p =>
    obtain ⟨a, last⟩ := p
    rw [hv] at hy
    have he : ([tk .mapping ++ parens
      (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ a.flatten ++ optToks idt vn)], last) =
        (items, rest) := Option.some.inj hy
    cases he
    change Region paramStop ((tk .mapping ++ parens
      (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ a.flatten ++ optToks idt vn)) ++ [])
    rw [List.append_nil]
    exact mapping_region key kn vn a.flatten (hvalue input a rest hv)

theorem yield_array_region (base : Syn .typeName) (len : Syn (.opt .expr))
    (hbase : TypeYieldRegion base) (hLength : LengthBalance len) : TypeYieldRegion (.array base len) := by
  intro input items rest hy
  change (base.yield input >>= fun p => len.yield p.2 >>= fun l =>
    some ([p.1.flatten ++ pu .lbrack ++ l.1.flatten ++ pu .rbrack], l.2)) = some (items, rest) at hy
  cases hb : base.yield input with
  | none => rw [hb] at hy; cases hy
  | some p =>
    obtain ⟨a, middle⟩ := p
    rw [hb] at hy
    change (len.yield middle >>= fun l =>
      some ([a.flatten ++ pu .lbrack ++ l.1.flatten ++ pu .rbrack], l.2)) = some (items, rest) at hy
    cases hl : len.yield middle with
    | none => rw [hl] at hy; cases hy
    | some l =>
      obtain ⟨b, last⟩ := l
      rw [hl] at hy
      have he : ([a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack], last) =
          (items, rest) := Option.some.inj hy
      cases he
      change Region paramStop ((a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack) ++ [])
      rw [List.append_nil]
      exact array_region a.flatten b.flatten (hbase input a middle hb)
        (hLength middle b rest hl)

theorem yield_fnType_region (ps : Syn (.list .param)) (vis : Option Visibility)
    (mu : Option Mutability) (rs : Syn (.list .param))
    (hparams : ParamsYieldRegions ps) (hreturns : ParamsYieldRegions rs) : TypeYieldRegion (.fnType ps vis mu rs) := by
  intro input items rest hy
  cases input with
  | nil => cases hy
  | cons choice input =>
    cases choice with
    | frags lens => cases hy
    | layoutFirst b => cases hy
    | attrs order =>
      change (ps.yield input >>= fun p =>
        attrsP (single .vis (optToks Visibility.toks vis) ++
          single .mutab (optToks Mutability.toks mu)) [] order p.2 >>= fun a =>
        rs.yield a.2 >>= fun r => some ([tk .function ++ parens (commaSep p.1) ++ a.1 ++
          (if r.1.isEmpty then [] else tk .returns ++ parens (commaSep r.1))], r.2)) =
            some (items, rest) at hy
      cases hp : ps.yield input with
      | none => rw [hp] at hy; cases hy
      | some p =>
        obtain ⟨a, middle⟩ := p
        rw [hp] at hy
        change ((arrange order (single .vis (optToks Visibility.toks vis) ++
            single .mutab (optToks Mutability.toks mu)) []).map (fun ts => (ts, middle)) >>= fun ats =>
          rs.yield ats.2 >>= fun r => some ([tk .function ++ parens (commaSep a) ++ ats.1 ++
            (if r.1.isEmpty then [] else tk .returns ++ parens (commaSep r.1))], r.2)) =
              some (items, rest) at hy
        cases hat : arrange order (single .vis (optToks Visibility.toks vis) ++
            single .mutab (optToks Mutability.toks mu)) [] with
        | none => rw [hat] at hy; cases hy
        | some attrs =>
          rw [hat] at hy
          change (rs.yield middle >>= fun r =>
            some ([tk .function ++ parens (commaSep a) ++ attrs ++
              (if r.1.isEmpty then [] else tk .returns ++ parens (commaSep r.1))], r.2)) =
                some (items, rest) at hy
          cases hr : rs.yield middle with
          | none => rw [hr] at hy; cases hy
          | some r =>
            obtain ⟨b, last⟩ := r
            rw [hr] at hy
            have he : ([tk .function ++ parens (commaSep a) ++ attrs ++
                (if b.isEmpty then [] else tk .returns ++ parens (commaSep b))], last) =
                  (items, rest) := Option.some.inj hy
            cases he
            change Region paramStop ((tk .function ++ parens (commaSep a) ++ attrs ++
              (if b.isEmpty then [] else tk .returns ++ parens (commaSep b))) ++ [])
            rw [List.append_nil]
            exact function_region a b vis mu order attrs
              (hparams input a middle hp)
              (hreturns middle b rest hr) hat

theorem yield_param_region (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (hType : TypeYieldRegion t) : ParamYieldRegion (.param t loc name) := by
  intro input items rest hy
  change (t.yield input >>= fun p => some
    ([p.1.flatten ++ optToks DataLoc.toks loc ++ optToks idt name], p.2)) = some (items, rest) at hy
  cases ht : t.yield input with
  | none => rw [ht] at hy; cases hy
  | some p =>
    obtain ⟨a, last⟩ := p
    rw [ht] at hy
    have he : ([a.flatten ++ optToks DataLoc.toks loc ++ optToks idt name], last) =
        (items, rest) := Option.some.inj hy
    cases he
    change Region paramStop ((a.flatten ++ optToks DataLoc.toks loc ++ optToks idt name) ++ [])
    rw [List.append_nil]
    exact param_region a.flatten loc name (hType input a rest ht)

theorem yield_params_nil : ParamsYieldRegions .nil := by
  intro input items rest hy
  have he : (([] : List (List Tok)), input) = (items, rest) := Option.some.inj hy
  cases he
  intro item hm
  cases hm

theorem yield_params_cons (p : Syn .param) (ps : Syn (.list .param))
    (hParam : ParamYieldRegion p) (hParams : ParamsYieldRegions ps) : ParamsYieldRegions (.cons p ps) := by
  intro input items rest hy
  obtain ⟨a, b, middle, hp, hs, hi⟩ := params_cons_decompose p ps input rest items hy
  have hhead : Region paramStop a.flatten := hParam input a middle hp
  have htail : ∀ item ∈ b, Region paramStop item := hParams middle b rest hs
  rw [hi]
  intro item hm
  obtain he | ht := List.mem_cons.mp hm
  · cases he
    exact hhead
  · exact htail item ht

theorem type_yield_region (t : Syn .typeName) (ha : TypeAtomsBalanced t)
    (input : List Choice) (items : List (List Tok)) (rest : List Choice)
    (hy : t.yield input = some (items, rest)) : Region paramStop items.flatten := by
  exact TypeAtomsBalanced.rec
    (motive_1 := fun t _ => TypeYieldRegion t)
    (motive_2 := fun p _ => ParamYieldRegion p)
    (motive_3 := fun ps _ => ParamsYieldRegions ps)
    (elem := yield_elem_region)
    (userType := yield_userType_region)
    (array := fun t len _ hl ht => yield_array_region t len ht hl)
    (mapping := fun key kn v vn _ hv => yield_mapping_region key kn v vn hv)
    (fnType := fun ps vis mu rs _ _ hp hr => yield_fnType_region ps vis mu rs hp hr)
    (param := fun t loc name _ ht => yield_param_region t loc name ht)
    (nil := yield_params_nil)
    (cons := fun p ps _ _ hp hs => yield_params_cons p ps hp hs)
    ha input items rest hy

theorem param_yield_region (p : Syn .param) (ha : ParamAtomsBalanced p)
    (input : List Choice) (items : List (List Tok)) (rest : List Choice)
    (hy : p.yield input = some (items, rest)) : Region paramStop items.flatten := by
  exact ParamAtomsBalanced.rec
    (motive_1 := fun t _ => TypeYieldRegion t)
    (motive_2 := fun p _ => ParamYieldRegion p)
    (motive_3 := fun ps _ => ParamsYieldRegions ps)
    (elem := yield_elem_region)
    (userType := yield_userType_region)
    (array := fun t len _ hl ht => yield_array_region t len ht hl)
    (mapping := fun key kn v vn _ hv => yield_mapping_region key kn v vn hv)
    (fnType := fun ps vis mu rs _ _ hp hr => yield_fnType_region ps vis mu rs hp hr)
    (param := fun t loc name _ ht => yield_param_region t loc name ht)
    (nil := yield_params_nil)
    (cons := fun p ps _ _ hp hs => yield_params_cons p ps hp hs)
    ha input items rest hy

theorem params_yield_regions (ps : Syn (.list .param)) (ha : ParamsAtomsBalanced ps)
    (input : List Choice) (items : List (List Tok)) (rest : List Choice)
    (hy : ps.yield input = some (items, rest)) : ∀ item ∈ items, Region paramStop item := by
  exact ParamsAtomsBalanced.rec
    (motive_1 := fun t _ => TypeYieldRegion t)
    (motive_2 := fun p _ => ParamYieldRegion p)
    (motive_3 := fun ps _ => ParamsYieldRegions ps)
    (elem := yield_elem_region)
    (userType := yield_userType_region)
    (array := fun t len _ hl ht => yield_array_region t len ht hl)
    (mapping := fun key kn v vn _ hv => yield_mapping_region key kn v vn hv)
    (fnType := fun ps vis mu rs _ _ hp hr => yield_fnType_region ps vis mu rs hp hr)
    (param := fun t loc name _ ht => yield_param_region t loc name ht)
    (nil := yield_params_nil)
    (cons := fun p ps _ _ hp hs => yield_params_cons p ps hp hs)
    ha input items rest hy

/-- All closing delimiter kinds and commas are outer type boundaries. -/
def typeStop (t : Tok) : Bool :=
  match mark t with
  | .closing _ => true
  | .opening _ => false
  | .plain => paramStop t

theorem region_all_closes (ts : List Tok) (h : Region paramStop ts) : Region typeStop ts := by
  induction h with
  | nil => exact .nil
  | atom t rest hm hs hr ih =>
    apply Region.atom t rest hm _ ih
    rw [typeStop, hm]
    exact hs
  | group d inside rest hs hb hr ih =>
    apply Region.group d inside rest _ hb ih
    rw [typeStop, mark_open]

theorem type_toks_region (t : Syn .typeName) (ha : TypeAtomsBalanced t)
    (choices : List Choice) (ts : List Tok) (h : t.toks choices = some ts) :
    Region typeStop ts := by
  unfold Syn.toks at h
  cases hy : t.yield choices with
  | none => rw [hy] at h; cases h
  | some p =>
    obtain ⟨items, rest⟩ := p
    rw [hy] at h
    cases rest with
    | cons c cs => cases h
    | nil =>
      have he : items.flatten = ts := Option.some.inj h
      cases he
      exact region_all_closes _ (type_yield_region t ha choices items [] hy)

/-- Actual type yields construct an exact scanner decomposition. -/
theorem type_toks_boundary (t : Syn .typeName) (ha : TypeAtomsBalanced t)
    (choices : List Choice) (ts suffix : List Tok)
    (ht : t.toks choices = some ts) (hs : StartsBoundary typeStop suffix) :
    cut typeStop [] (ts ++ suffix) = some (ts, suffix) := by
  exact region_cut_boundary typeStop ts suffix (type_toks_region t ha choices ts ht) hs

/-- Actual type token prefixes and boundary suffixes have unique decomposition.
This asserts token equality, not identity of embedded expression atoms. -/
theorem type_token_boundary_unique (left right : Syn .typeName)
    (hl : TypeAtomsBalanced left) (hr : TypeAtomsBalanced right)
    (ll rl : List Choice) (lt rt ls rs : List Tok)
    (hyl : left.toks ll = some lt) (hyr : right.toks rl = some rt)
    (hsl : StartsBoundary typeStop ls) (hsr : StartsBoundary typeStop rs)
    (same : lt ++ ls = rt ++ rs) : lt = rt ∧ ls = rs := by
  exact boundary_unique typeStop lt rt ls rs (type_toks_region left hl ll lt hyl)
    (type_toks_region right hr rl rt hyr) hsl hsr same

theorem dynamic_atoms_balanced (n : Nat) : TypeAtomsBalanced (dynamicType n) := by
  induction n with
  | zero => exact .elem .bool
  | succ n ih => exact .array _ _ ih no_length_balance

/-- Inhabited actual-type boundary control at every array nesting depth. -/
theorem dynamic_type_boundary (n : Nat) (suffix : List Tok)
    (hs : StartsBoundary typeStop suffix) :
    cut typeStop [] ((dynamicItems n).flatten ++ suffix) =
      some ((dynamicItems n).flatten, suffix) := by
  exact type_toks_boundary (dynamicType n) (dynamic_atoms_balanced n) []
    (dynamicItems n).flatten suffix
    (exact_toks _ _ _ (exact_dynamic_depth n)) hs

/-- The actual nested mapping/function/array control satisfies the local atom
contract. No source-level type admission or expression evaluation is used. -/
theorem nested_atoms_balanced : TypeAtomsBalanced nestedLayoutType := by
  apply TypeAtomsBalanced.array
  · apply TypeAtomsBalanced.mapping
    apply TypeAtomsBalanced.fnType
    · exact .cons _ _ (.param _ _ _ (.array _ _ (.elem .bool) no_length_balance)) .nil
    · exact .cons _ _ (.param _ _ _ (.elem .bool)) .nil
  · exact no_length_balance

theorem every_close_boundary (d : Delim) (rest : List Tok) :
    StartsBoundary typeStop (closeToken d :: rest) := by
  refine Or.inr ⟨closeToken d, rest, rfl, ?_⟩
  rw [typeStop, mark_close]

/-- The remainder following the first item includes its comma, if present. -/
def afterFirst (tail : List (List Tok)) (suffix : List Tok) : List Tok :=
  match tail with
  | [] => suffix
  | next :: rest => .punct .comma :: (commaSep (next :: rest) ++ suffix)

theorem commaSep_split (head : List Tok) (tail : List (List Tok)) (suffix : List Tok) :
    commaSep (head :: tail) ++ suffix = head ++ afterFirst tail suffix := by
  cases tail with
  | nil =>
    change (head ++ []) ++ suffix = head ++ suffix
    rw [List.append_nil]
  | cons next rest =>
    change (head ++ (pu .comma ++ commaSep (next :: rest))) ++ suffix =
      head ++ (.punct .comma :: (commaSep (next :: rest) ++ suffix))
    simp only [List.append_assoc, pu, List.cons_append, List.nil_append]

theorem afterFirst_boundary (tail : List (List Tok)) (suffix : List Tok)
    (hs : StartsBoundary paramStop suffix) : StartsBoundary paramStop (afterFirst tail suffix) := by
  cases tail with
  | nil => exact hs
  | cons next rest =>
    exact Or.inr ⟨.punct .comma, commaSep (next :: rest) ++ suffix, rfl, rfl⟩

/-- First-item decomposition for an actual successful nonempty parameter list. -/
theorem params_first_boundary (ps : Syn (.list .param)) (ha : ParamsAtomsBalanced ps)
    (choices rest : List Choice) (head : List Tok) (tail : List (List Tok))
    (hy : ps.yield choices = some (head :: tail, rest)) (suffix : List Tok)
    (hs : StartsBoundary paramStop suffix) :
    cut paramStop [] (commaSep (head :: tail) ++ suffix) =
      some (head, afterFirst tail suffix) := by
  rw [commaSep_split]
  apply region_cut_boundary
  · exact params_yield_regions ps ha choices (head :: tail) rest hy head List.mem_cons_self
  · exact afterFirst_boundary tail suffix hs

/-- The existing nested intrinsic type has an inhabited exact boundary split. -/
theorem nested_type_boundary (suffix : List Tok) (hs : StartsBoundary typeStop suffix) :
    ∃ ts : List Tok, nestedLayoutType.toks [.attrs [.vis, .mutab]] = some ts ∧
      cut typeStop [] (ts ++ suffix) = some (ts, suffix) := by
  have hy := exact_toks _ _ _ exact_nested_layout
  refine ⟨_, hy, ?_⟩
  exact type_toks_boundary nestedLayoutType nested_atoms_balanced _ _ suffix hy hs

/-- Wrong/missing layouts fail actual producer yield; no parser is mocked. -/
theorem malformed_layouts_refused :
    (Syn.fnType .nil none none .nil).toks [] = none ∧
    nestedLayoutType.toks [.attrs [.vis]] = none ∧
    nestedLayoutType.toks [.frags []] = none := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms elem_region
#print axioms path_tail_region
#print axioms path_region
#print axioms name_region
#print axioms loc_region
#print axioms vis_region
#print axioms mut_region
#print axioms key_region
#print axioms parens_region
#print axioms brackets_region
#print axioms commaSep_balanced
#print axioms param_region
#print axioms array_region
#print axioms mapping_region
#print axioms arrange_cons_nil
#print axioms arrange_region
#print axioms single_region
#print axioms fn_attrs_region
#print axioms function_region
#print axioms atoms_elem_iff
#print axioms atoms_userType_iff
#print axioms atoms_array_iff
#print axioms atoms_mapping_iff
#print axioms atoms_fnType_iff
#print axioms atoms_param_iff
#print axioms atoms_params_nil_iff
#print axioms atoms_params_cons_iff
#print axioms no_length_balance
#print axioms some_length_balance
#print axioms numeric_length_balance
#print axioms yield_elem_region
#print axioms yield_userType_region
#print axioms yield_mapping_region
#print axioms yield_array_region
#print axioms yield_fnType_region
#print axioms yield_param_region
#print axioms yield_params_nil
#print axioms yield_params_cons
#print axioms type_yield_region
#print axioms param_yield_region
#print axioms params_yield_regions
#print axioms region_all_closes
#print axioms type_toks_region
#print axioms type_toks_boundary
#print axioms type_token_boundary_unique
#print axioms dynamic_atoms_balanced
#print axioms dynamic_type_boundary
#print axioms nested_atoms_balanced
#print axioms every_close_boundary
#print axioms commaSep_split
#print axioms afterFirst_boundary
#print axioms params_first_boundary
#print axioms nested_type_boundary
#print axioms malformed_layouts_refused

end Solidity.Frontend.TypeGrammarH28.TypeRegion
