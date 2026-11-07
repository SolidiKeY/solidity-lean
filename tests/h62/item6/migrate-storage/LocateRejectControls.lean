import Lean

/-! Parameter-only copies of the frozen layout vocabulary and locate function.
Test-only rejection coverage; no production theorem or premise is edited.
The word/nonempty contradiction is the exact elimination boundary at line376.
-/
namespace StorageMigrationLocateFixture
inductive Loc where
  | root (off : Nat)
  | hash (k : Nat) (s : Loc) (off : Nat)
  | data (s : Loc) (off : Nat)
  deriving DecidableEq, Repr

def Loc.add : Loc → Nat → Loc
  | .root o, i => .root (o + i)
  | .hash k s o, i => .hash k s (o + i)
  | .data s o, i => .data s (o + i)

def lmax : Nat := 2 ^ 64
inductive STy where
  | word
  | strct (fs : List STy)
  | sarr (e : STy) (n : Nat)
  | darr (e : STy)
  | map (v : STy)
  deriving Repr
mutual
def STy.size : STy → Nat
  | .word => 1
  | .strct fs => STy.sizes fs
  | .sarr e n => n * e.size
  | .darr _ => 1
  | .map _ => 1
def STy.sizes : List STy → Nat
  | [] => 0
  | t :: ts => t.size + STy.sizes ts
end
inductive Step where
  | field (i : Nat)
  | index (i : Nat)
  | key (k : Nat)
  deriving DecidableEq, Repr

def STy.locate : STy → Loc → List Step → Option (STy × Loc)
  | t, l, [] => some (t, l)
  | .strct fs, l, .field i :: p =>
    match fs[i]? with
    | some t => t.locate (l.add (STy.sizes (fs.take i))) p
    | none => none
  | .sarr e n, l, .index i :: p => if i < n then e.locate (l.add (i * e.size)) p else none
  | .darr e, l, .index i :: p => if i < lmax then e.locate (.data l (i * e.size)) p else none
  | .map v, l, .key k :: p => v.locate (.hash k l 0) p
  | _, _, _ :: _ => none

/-- Every invalid constructor/step combination from the original theorem. -/
def InvalidHead : STy → Step → Prop
  | .word, _ => True
  | .strct _, .index _ => True
  | .strct _, .key _ => True
  | .sarr _ _, .field _ => True
  | .sarr _ _, .key _ => True
  | .darr _, .field _ => True
  | .darr _, .key _ => True
  | .map _, .field _ => True
  | .map _, .index _ => True
  | _, _ => False

theorem invalid_head_rejects (t : STy) (l : Loc) (s : Step) (p : List Step)
    (bad : InvalidHead t s) : t.locate l (s :: p) = none := by
  cases t <;> cases s <;> simp only [InvalidHead] at bad <;> rfl

/-- Explicit step elimination discharges all three word/nonempty cases. -/
theorem word_nonempty_impossible (l : Loc) (s : Step) (p : List Step)
    (t' : STy) (l' : Loc) (h : STy.word.locate l (s :: p) = some (t', l')) : False := by
  cases s <;> cases h

theorem empty_path_accepts (t : STy) (l : Loc) : t.locate l [] = some (t, l) := by
  cases t <;> rfl

example (l : Loc) : (STy.strct []).locate l [.field 0] = none := rfl
example (l : Loc) : (STy.sarr .word 0).locate l [.index 0] = none := rfl
example (l : Loc) : (STy.darr .word).locate l [.index lmax] = none := by
  simp only [STy.locate, Nat.lt_irrefl, ↓reduceIte]
example (l : Loc) (k : Nat) :
    (STy.map .word).locate l [.key k] = some (.word, .hash k l 0) := rfl
end StorageMigrationLocateFixture

#print axioms StorageMigrationLocateFixture.invalid_head_rejects
#print axioms StorageMigrationLocateFixture.word_nonempty_impossible
#print axioms StorageMigrationLocateFixture.empty_path_accepts
