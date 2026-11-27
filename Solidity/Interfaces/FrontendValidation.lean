import Solidity.Frontend.SolcJson.Contract
import Solidity.Frontend.SolcJson.TryPanicSourceCaller
import Solidity.Frontend.SolcJson.CallMetadataPath
import Solidity.Frontend.SolcJson.YulBuiltinUse
import Solidity.Frontend.SolcJson.YulAttachedUse
import Solidity.SolcValidation.DataLayout
import Solidity.SolcValidation.IrCensusUnique
import Solidity.SolcValidation.IrCensusParse
import Solidity.SolcValidation.IrRename

/-! Fixed structural postconditions, separated from external compiler execution.
These are specification propositions, not proofs or execution assumptions. -/
namespace Solidity.Interfaces.FrontendValidation
open Lean Solidity.Frontend Solidity.SolcValidation.IrSyntax
/-- Typed JSON access preserves the original field and its value. -/
def JsonFields : Prop :=
  (∀ j k v, J.get j k = .ok v → j.getObjVal? k = .ok v) ∧ (∀ j k v, J.opt j k = some v → j.getObjVal? k = .ok v ∧ v ≠ .null) ∧ (∀ j k s, J.str j k = .ok s → j.getObjVal? k = .ok (.str s)) ∧
  (∀ j k xs, J.arr j k = .ok xs → j.getObjVal? k = .ok (.arr xs.toArray)) ∧ (∀ j k s, J.str? j k = some s → j.getObjVal? k = .ok (.str s)) ∧ (∀ j k xs, J.arr? j k = some xs → j.getObjVal? k = .ok (.arr xs)) ∧
  (∀ j i, J.ref? j = some i → j.getObjValAs? Int "referencedDeclaration" = .ok i) ∧ (∀ j i, J.id? j = some i → j.getObjValAs? Int "id" = .ok i) ∧
  (∀ j k i, TryPanicSourcePlan.intField j k = some i → j.getObjValAs? Int k = .ok i) ∧ (∀ j k b, TryPanicSourcePlan.boolField j k = some b → j.getObjValAs? Bool k = .ok b) ∧
  (∀ j k i v, TryPanicSourcePlan.memberAt j k i = some v → ∃ xs, J.arr? j k = some xs ∧ xs[i]? = some v)

/-- Accepted byte spellings: printable ASCII or the explicit supported escapes; surrogates are not excluded. -/
inductive DecodedBytes : List Char → List Nat → Prop where
  | nil : DecodedBytes [] []
  | ascii {c : Char} {cs bs} : 32 ≤ c.toNat → c.toNat < 127 → c.toNat ≠ 34 → c.toNat ≠ 92 → DecodedBytes cs bs → DecodedBytes (c :: cs) (c.toNat :: bs)
  | simple {c : Char} {b cs bs} : (c.toNat, b) ∈ [(92,92),(34,34),(39,39),(110,10),(114,13),(116,9),(98,8),(102,12),(118,11)] → DecodedBytes cs bs → DecodedBytes (Char.ofNat 92 :: c :: cs) (b :: bs)
  | hex {a b : Char} {x y cs bs} : hexDigit? a = some x → hexDigit? b = some y → DecodedBytes cs bs → DecodedBytes (Char.ofNat 92 :: 'x' :: a :: b :: cs) ((16 * x + y) :: bs)
  | unicode {a b c d : Char} {w x y z cs bs} : hexDigit? a = some w → hexDigit? b = some x → hexDigit? c = some y → hexDigit? d = some z →
    DecodedBytes cs bs → DecodedBytes (Char.ofNat 92 :: 'u' :: a :: b :: c :: d :: cs)
      ((let n := ((w * 16 + x) * 16 + y) * 16 + z; if n < 128 then [n] else if n < 2048 then [192 + n / 64, 128 + n % 64] else [224 + n / 4096, 128 + n / 64 % 64, 128 + n % 64]) ++ bs)
/-- Scalar decoding and binder admission retain exact values and freshness. -/
def IrAtoms : Prop :=
  (∀ n b, toByte? n = some b → b.val = n) ∧
  (∀ c d, hexDigit? c = some d → d < 16 ∧ ((d < 10 ∧ c.toNat = 48 + d) ∨ (10 ≤ d ∧ (c.toNat = 87 + d ∨ c.toNat = 55 + d)))) ∧
  (∀ bs w, stringWord bs = some w → bs.length ≤ 32 ∧ w.val = bytesValue bs * 256 ^ (32 - bs.length)) ∧
  (∀ L x m, findVar L x = some m → m.index = L.idxOf x) ∧
  (∀ F x s, findFn F x = some s → s.1.name = x ∧ s.2.index = (F.map FnSig.name).idxOf x) ∧
  (∀ L xs, freshNames L xs = .ok () → xs.Nodup ∧ ∀ x ∈ xs, x ∉ L ∧ reserved x = false) ∧
  (∀ ss, namesNodup ss = true → (ss.map FnSig.name).Nodup) ∧
  (∀ c b, escapeByte c = some b → DecodedBytes [Char.ofNat 92, c] [b.val]) ∧
  (∀ cs bs, decodeString cs = some bs → DecodedBytes cs (bs.map Fin.val)) ∧
  (∀ (tok : LitTok) w, tok.decode = some w → match tok with
    | .num n => w.val = n
    | .bool b => w.val = if b then 1 else 0
    | .hex bs => bs.length ≤ 32 ∧ w.val = bytesValue bs * 256 ^ (32 - bs.length)
    | .str raw => ∃ bs, decodeString raw.toList = some bs ∧ stringWord bs = some w)
/-- Reduced fractions and exact cross-multiplied arithmetic, with no claim
about malformed input denominators being positive. -/
def Canonical (q : Q) : Prop := 0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1
def RationalChecks : Prop :=
  (∀ n d q, Q.make n d = some q → d ≠ 0 ∧ Canonical q ∧ q.num * d = n * q.den) ∧
  (∀ a b q, Q.add a b = some q → Canonical q ∧ q.num * (a.den * b.den : Nat) = (a.num * b.den + b.num * a.den) * q.den) ∧
  (∀ a b q, Q.sub a b = some q → Canonical q ∧ q.num * (a.den * b.den : Nat) = (a.num * b.den - b.num * a.den) * q.den) ∧
  (∀ a b q, Q.mul a b = some q → Canonical q ∧ q.num * (a.den * b.den : Nat) = (a.num * b.num) * q.den) ∧
  (∀ a b q, Q.div a b = some q → Canonical q ∧ q.num * (a.den * b.num) = (a.num * b.den) * q.den) ∧
  (∀ a n, Q.int? a = some n → a.den = 1 ∧ a.num = n) ∧
  (∀ j q, constVal j = some q → Canonical q) ∧
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
/-- Independent literal adapters preserve numeric shape, spelling and decoded value. -/
def SourceLiterals : Prop :=
  (∀ s n, TryPanicSourcePlan.unsignedText? s = some n → parseRational s = some (Q.ofInt n) ∧
    if s.startsWith "0x" || s.startsWith "0X" then 0 < (s.toList.drop 2).length ∧ (s.toList.drop 2).length % 2 = 0 else s ≠ "" ∧ s.toList.all Char.isDigit = true) ∧
  (∀ (check : Json → Option Solidity.Evm.TryByteImage.U256) kind, (check, kind) ∈
    [(TryPanicSourcePlan.literal?, "YulLiteral"), (TryPanicSourceCaller.argument?, "Literal")] →
    ∀ node v, check node = some v → J.kind node = kind ∧ J.str? node "kind" = some "number" ∧
    ∃ spelling n, J.str? node "value" = some spelling ∧ TryPanicSourcePlan.unsignedText? spelling = some n ∧ v.val = (n : Int))
/-- Whole-reader preservation of recorded refusals and declaration identities. -/
def ReaderRetainsChecks (c : SolcContract) : Prop :=
  (∀ f ∈ c.funs, ∀ body, f.body = .ok body → f.sourceScope.diagnostic? = none ∧ ∃ info, f.sourceDecl = some info ∧ (f.name, info) ∈ c.sourceDecls) ∧
  (∀ f ∈ c.funs ++ c.ctor.toList, ∀ info, f.sourceDecl = some info → (f.name, info) ∈ c.sourceDecls) ∧
  (∀ gap, c.initGap = some gap → c.initMembers = c.members ∧ ∃ ctor, c.ctor = some ctor ∧ ∃ refusal, ctor.body = .error refusal)
def ReaderChecks : Prop :=
  ∀ ast name ren testing rewriteSpec rewriteLoop scanSource scanLoop readsSpec entrypoints viaIR
    compilerCode namedErrorSourceOrder compilationUnits result,
    readContract ast name ren testing rewriteSpec rewriteLoop scanSource scanLoop readsSpec
      entrypoints viaIR compilerCode namedErrorSourceOrder compilationUnits = .ok result →
    result.name = name ∧ ReaderRetainsChecks result
/-- Metadata is tied to the supplied declaration table and, when provided, AST paths. -/
def CallChecks : Prop :=
  (∀ fixture p, CallMetadata.readProfile fixture = .ok p → p.fixture = fixture ∧
    fixture.getObjVal? "ast" = .ok p.ast ∧ Source.read fixture p.ast = .ok p.provenance) ∧
  (∀ profile declarations call result, CallMetadata.inspect profile declarations call = .ok result →
    result.call = call ∧ result.declaration ∈ declarations ∧
    (result.isStatic = true → CallMetadata.staticTarget? result.profile = some true ∧
      ((result.declaration.getObjValAs? String "stateMutability").toOption = some "pure" ∨
       (result.declaration.getObjValAs? String "stateMutability").toOption = some "view"))) ∧
  (∀ profile declarations call result, CallMetadata.attachPaths profile declarations call = .ok result →
    CallMetadata.walk profile.ast call = some result.checked.info.call ∧
    result.declarations.map CallMetadata.Located.path = declarations)

def JsonText {ε : Type} {P : String → Json → Type} (check : (raw : String) → Except ε ((node : Json) × P raw node)) : Prop :=
  ∀ raw r, check raw = .ok r → Json.parse raw = .ok r.1
/-- Independent checked roots retain their distinct static/safety boundaries.
Only PROVIDED references receive forward accounting; completeness is separate. -/
def YulChecks : Prop :=
  (∀ X entries table, @YulJson.checkDeclarationTable X entries = some table → table.entries = entries ∧ (entries.map YulJson.Declaration.id).Nodup) ∧
  (∀ F X n E, JsonText (@YulJson.checkExpressionText F X n E)) ∧
  JsonText YulJson.parseBlockText ∧ JsonText YulJson.checkBlockShapeText ∧
  (∀ X table names input outside locals, JsonText (@YulJson.ScopedJson.checkText X table names input outside locals)) ∧
  (∀ X table names input outside locals, JsonText (@YulJson.ForwardJson.checkText X table names input outside locals)) ∧
  (∀ X table names input outside locals, JsonText (@YulJson.BuiltinGuard.checkJsonText X table names input outside locals)) ∧
  (∀ outside, JsonText (YulJson.Words.checkText outside)) ∧
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
  (∀ root, parsesTo text root = true → ∃ p, parse text = .ok p ∧ p.parts.root = root) ∧
  (∀ p, parse text = .ok p → lex text = some (objectToks p.parts.root) ∧ objectWf p.parts.root = true) ∧
  (∀ F G c L (ρ : Ren F G) (b : Block F c L) b', b.ren ρ = some b' → b.toks = b'.toks) ∧
  (∀ artifact entries label selected, @Solidity.SolcValidation.selectData artifact label entries = some selected →
    (label, selected.ref) ∈ entries ∧ selected.ref.bytes.length = selected.ref.size.val)
end Solidity.Interfaces.FrontendValidation
