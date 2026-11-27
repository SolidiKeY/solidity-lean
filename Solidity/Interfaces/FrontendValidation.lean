import Solidity.Frontend.SolcJson.Contract
import Solidity.Frontend.SolcJson.CallMetadataPath
import Solidity.Frontend.SolcJson.YulBuiltinUse
import Solidity.Frontend.SolcJson.YulAttachedUse
import Solidity.SolcValidation.DataLayout
import Solidity.SolcValidation.IrCensusUnique
import Solidity.SolcValidation.IrRename

/-! Fixed structural postconditions, separated from external compiler execution.
These are specification propositions, not proofs or execution assumptions. -/
namespace Solidity.Interfaces.FrontendValidation
open Lean Solidity.Frontend Solidity.SolcValidation.IrSyntax

/-- Typed JSON access preserves the original field and its value. -/
def JsonFields : Prop :=
  (∀ j k v, J.get j k = .ok v → j.getObjVal? k = .ok v) ∧
  (∀ j k v, J.opt j k = some v → j.getObjVal? k = .ok v ∧ v ≠ .null) ∧
  (∀ j k s, J.str j k = .ok s → j.getObjVal? k = .ok (.str s)) ∧
  (∀ j k xs, J.arr j k = .ok xs → j.getObjVal? k = .ok (.arr xs.toArray)) ∧
  (∀ j k s, J.str? j k = some s → j.getObjVal? k = .ok (.str s)) ∧
  (∀ j k xs, J.arr? j k = some xs → j.getObjVal? k = .ok (.arr xs)) ∧
  (∀ j i, J.ref? j = some i → j.getObjValAs? Int "referencedDeclaration" = .ok i) ∧
  (∀ j i, J.id? j = some i → j.getObjValAs? Int "id" = .ok i)

/-- Scalar decoding and binder admission retain exact values and freshness. -/
def IrAtoms : Prop :=
  (∀ n b, toByte? n = some b → b.val = n) ∧
  (∀ c d, hexDigit? c = some d → d < 16 ∧
    ((d < 10 ∧ c.toNat = 48 + d) ∨
      (10 ≤ d ∧ (c.toNat = 87 + d ∨ c.toNat = 55 + d)))) ∧
  (∀ bs w, stringWord bs = some w →
    bs.length ≤ 32 ∧ w.val = bytesValue bs * 256 ^ (32 - bs.length)) ∧
  (∀ L x m, findVar L x = some m → m.index = L.idxOf x) ∧
  (∀ F x s, findFn F x = some s → s.1.name = x ∧
    s.2.index = (F.map FnSig.name).idxOf x) ∧
  (∀ L xs, freshNames L xs = .ok () →
    xs.Nodup ∧ ∀ x ∈ xs, x ∉ L ∧ reserved x = false) ∧
  (∀ ss, namesNodup ss = true → (ss.map FnSig.name).Nodup)

/-- Reduced fractions and exact cross-multiplied arithmetic, with no claim
about malformed input denominators being positive. -/
def Canonical (q : Q) : Prop := 0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1

def RationalChecks : Prop :=
  (∀ n d q, Q.make n d = some q → d ≠ 0 ∧ Canonical q ∧ q.num * d = n * q.den) ∧
  (∀ a b q, Q.add a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.den + b.num * a.den) * q.den) ∧
  (∀ a b q, Q.sub a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.den - b.num * a.den) * q.den) ∧
  (∀ a b q, Q.mul a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.num) * q.den) ∧
  (∀ a b q, Q.div a b = some q → Canonical q ∧
    q.num * (a.den * b.num) = (a.num * b.den) * q.den) ∧
  (∀ a n, Q.int? a = some n → a.den = 1 ∧ a.num = n) ∧
  (∀ a e q, Q.pow a e = some q → e.den = 1 ∧
    if e.num = 0 then q = Q.ofInt 1 else if a.num = 0 then q = Q.ofInt 0 else
    ((1 < a.num.natAbs ∨ 1 < a.den) → (max (Nat.log2 a.num.natAbs) (Nat.log2 a.den) + 1) * e.num.natAbs ≤ 4096) ∧
    if e.num < 0 then Canonical q ∧ q.num * a.num ^ e.num.natAbs = (a.den : Int) ^ e.num.natAbs * q.den else
    q.num = a.num ^ e.num.natAbs ∧ q.den = a.den ^ e.num.natAbs) ∧
  (∀ s q, parseRational s = some q → Canonical q ∧ 0 ≤ q.num ∧
    let t := s.replace "_" "";
    if t.startsWith "0x" || t.startsWith "0X" then
      ∃ ds : List Nat, ds.length = (t.toList.drop 2).length ∧ (∀ (c : Char) (d : Nat), (c, d) ∈ List.zip (t.toList.drop 2) ds →
        d < 16 ∧ ((d < 10 ∧ c.toNat = 48 + d) ∨ (10 ≤ d ∧ (c.toNat = 87 + d ∨ c.toNat = 55 + d)))) ∧
        q.den = 1 ∧ q.num = (ds.foldl (fun n d => n * 16 + d) 0 : Nat) else
      ∃ m i f : String, ∃ e : Int, ∃ n : Nat,
        (((t.replace "E" "e").splitOn "e" = [m] ∧ e = 0) ∨ ∃ x, (t.replace "E" "e").splitOn "e" = [m, x] ∧
          (if x.startsWith "-" then (x.drop 1).toNat?.map (fun n => -(n : Int)) else x.toInt?) = some e) ∧
        (m.splitOn "." = [i] ∧ f = "" ∨ m.splitOn "." = [i, f]) ∧ (i ++ f) ≠ "" ∧ (i ++ f).toNat? = some n ∧ (n = 0 ∨ e.natAbs ≤ 4096) ∧
        q.num * (10 : Int) ^ (f.length + if e < 0 then e.natAbs else 0) = (n : Int) * 10 ^ (if e < 0 then 0 else e.natAbs) * q.den)

/-- Whole-reader preservation of recorded refusals and declaration identities. -/
def ReaderRetainsChecks (c : SolcContract) : Prop :=
  (∀ f ∈ c.funs, ∀ body, f.body = .ok body →
    f.sourceScope.diagnostic? = none ∧ ∃ info, f.sourceDecl = some info ∧ (f.name, info) ∈ c.sourceDecls) ∧
  (∀ f ∈ c.funs ++ c.ctor.toList, ∀ info, f.sourceDecl = some info → (f.name, info) ∈ c.sourceDecls) ∧
  (∀ gap, c.initGap = some gap → c.initMembers = c.members ∧
    ∃ ctor, c.ctor = some ctor ∧ ∃ refusal, ctor.body = .error refusal)

def ReaderChecks : Prop :=
  ∀ ast name ren testing rewriteSpec rewriteLoop scanSource scanLoop readsSpec entrypoints viaIR
    compilerCode namedErrorSourceOrder compilationUnits result,
    readContract ast name ren testing rewriteSpec rewriteLoop scanSource scanLoop readsSpec
      entrypoints viaIR compilerCode namedErrorSourceOrder compilationUnits = .ok result →
    result.name = name ∧ ReaderRetainsChecks result

/-- Metadata is tied to the supplied declaration table and, when provided, AST paths. -/
def CallChecks : Prop :=
  (∀ profile declarations call result, CallMetadata.inspect profile declarations call = .ok result →
    result.call = call ∧ result.declaration ∈ declarations ∧
    (result.isStatic = true → CallMetadata.staticTarget? result.profile = some true ∧
      ((result.declaration.getObjValAs? String "stateMutability").toOption = some "pure" ∨
       (result.declaration.getObjValAs? String "stateMutability").toOption = some "view"))) ∧
  (∀ profile declarations call result, CallMetadata.attachPaths profile declarations call = .ok result →
    CallMetadata.walk profile.ast call = some result.checked.info.call ∧
    result.declarations.map CallMetadata.Located.path = declarations)

/-- Independent checked roots retain their distinct static/safety boundaries.
Only PROVIDED references receive forward accounting; completeness is separate. -/
def YulChecks : Prop :=
  (∀ X table original input outside localNames bound node result,
    @YulJson.ScopedJson.check X table original input outside localNames bound node = .ok result →
    YulJson.metadata table node = .ok result.imported ∧
    YulJson.field node "AST" = .ok result.ast ∧ result.shaped.tree.prec = true ∧
    YulJson.MetadataSafetyD result.imported.flags result.imported.documentation ∧
    Nonempty (Solidity.Yul.ScopedSyntax.Prepared input.scope .A outside localNames result.shaped.tree)) ∧
  (∀ X table original input outside localNames bound node result,
    @YulJson.ForwardJson.check X table original input outside localNames bound node = .ok result →
    Nonempty (YulJson.ReferenceCover.All table original result.imported.ast result.imported.imported.references.entries)) ∧
  (∀ F X n E bound node (r : @YulJson.CheckedExpression F X n E bound node),
    YulJson.expression bound node = .ok r.tree ∧ Nonempty (Solidity.Yul.ExprD E r.tree r.arity)) ∧
  (∀ outside bound node (r : YulJson.Words.Checked outside bound node),
    r.imported.references.entries = [] ∧ YulJson.blockAux bound r.ast = .ok r.shaped.tree ∧
    r.shaped.tree.prec = true ∧ YulJson.MetadataSafetyD r.imported.flags r.imported.documentation ∧
    Nonempty (Solidity.Yul.WordSyntax.Prepared outside r.shaped.tree)) ∧
  (∀ X scope tier outside localNames doc src (r : @YulJson.ScopedParse.Checked X scope tier outside localNames doc src),
    (r.parsed.flags.filter (· == "memory-safe")).length ≤ 1 ∧
    YulJson.MetadataSafetyD r.parsed.flags doc ∧
    Nonempty (Solidity.Yul.ScopedSyntax.Prepared scope tier outside localNames r.parsed.body)) ∧
  (∀ X scope tier outside locals doc src (r : @YulJson.BuiltinGuard.Parsed X scope tier outside locals doc src),
    Nonempty (Solidity.Yul.BuiltinUse.Checked r.original.parsed.body)) ∧
  (∀ X table names input outside locals bound node (r : @YulJson.BuiltinGuard.JsonChecked X table names input outside locals bound node),
    Nonempty (Solidity.Yul.BuiltinUse.Checked r.original.imported.shaped.tree)) ∧
  (∀ root current table original write node reference attached scope n locals
    (r : @YulJson.ReferenceAttachment.Use root current table original write node reference attached scope n locals),
    Nonempty (Solidity.Yul.ScopeIndexD scope reference.declaration.index r.index) ∧
    (attached.suffix ≠ [] ∨ Solidity.Yul.NoBinding locals attached.visible))

/-- Full IR admission checks exact tokens/well-formedness; partial renaming
preserves tokens. Data lookup retains its actual bounded artifact interval. -/
def IrChecks (text : String) : Prop :=
  (∀ p, parse text = .ok p → lex text = some (objectToks p.parts.root) ∧ objectWf p.parts.root = true) ∧
  (∀ F G c L (ρ : Ren F G) (b : Block F c L) b', b.ren ρ = some b' → b.toks = b'.toks) ∧
  (∀ artifact entries label selected, @Solidity.SolcValidation.selectData artifact label entries = some selected →
    (label, selected.ref) ∈ entries ∧ selected.ref.bytes.length = selected.ref.size.val)

end Solidity.Interfaces.FrontendValidation
