import Solidity.Yul.Views.SourceMagicReads
import Solidity.Backend.Environment.Crypto

namespace Solidity.Yul.Views

/-- Reuse the actual target owner's converter. Distinct intrinsic Word types
are not identified, and no new machine-word representation is introduced. -/
def environmentWord (word : Roadmap.Word) : Backend.Environment.Word := Backend.Environment.wrap word.val

theorem environmentWord_nat (word : Roadmap.Word) : (environmentWord word).1.toNat=word.val := by
  rw [environmentWord,Backend.Environment.wrap_nat,Nat.mod_eq_of_lt word.isLt]

theorem environmentWord_injective : Function.Injective environmentWord := by
  intro a b same
  apply Fin.ext
  have values := congrArg (fun w : Backend.Environment.Word => w.1.toNat) same
  simpa only [environmentWord_nat] using values

/-- Account conversion is exact here BECAUSE the actual source Address is
already160bit bounded. This is not a cleanup policy for arbitrary dirty words. -/
def environmentAddress (address : Roadmap.Address) : ContractWorld.Address :=
  Backend.Environment.account (environmentWord (addressInputWord address))

theorem environmentAddress_word (address : Roadmap.Address) :
    (environmentAddress address).1=environmentWord (addressInputWord address) := by
  apply Subtype.ext
  unfold environmentAddress
  rw [Backend.Environment.account_value,environmentWord_nat]
  change ((address.val % 2^160 : Nat) : Int)=((address.val % 2^256 : Nat) : Int)
  have high : address.val < 2^256 := (addressInputWord address).isLt
  rw [Nat.mod_eq_of_lt address.isLt,Nat.mod_eq_of_lt high]

/-- Construct the EXISTING target Frame. The ledger is an explicit input;
there is no assumed source-world balance, own-balance or account-code law. -/
def sourceEnvironmentFrame {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) : Backend.Environment.Frame :=
  ⟨environmentAddress F.this,environmentAddress F.sender,environmentWord F.value,environmentWord G.timestamp,funds⟩

theorem sourceTarget_timestamp {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) :
    (uintValueOfWord E.layout G.timestamp).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .timestamp) := by
  rw [uintValueOfWord_word]
  rfl

theorem sourceTarget_sender {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) :
    (Source.Val.address (D := E.layout) (p := false) F.sender).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .msgSender) := by
  rw [sourceAddress_input_word]
  change some (environmentWord (addressInputWord F.sender))=some ((environmentAddress F.sender).1)
  rw [environmentAddress_word]

theorem sourceTarget_value {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) :
    (uintValueOfWord E.layout F.value).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .msgValue) := by
  rw [uintValueOfWord_word]
  rfl

/-- Self identity is the actual source Fr.this, not an invented source magic
expression. Target instruction selection/execution remains with its owner. -/
theorem sourceTarget_self {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) :
    Backend.Environment.observe (sourceEnvironmentFrame G F funds) .selfAddress=
      environmentWord (addressInputWord F.this) := environmentAddress_word F.this

theorem sourceTarget_transaction {E} (G : Source.Glob E) (F : Source.Fr)
    (funds : ContractWorld.Address → Backend.Environment.Word) (input : Environment) (tx : Source.TxConfig) :
    environmentWord ((input.bindTransaction tx).read .timestamp)=
      Backend.Environment.observe (sourceEnvironmentFrame { G with timestamp := tx.request.timestamp } F funds) .timestamp := rfl

/-- Concrete actual source evaluation AND actual target frame observations.
This is a state/input interface, not a lowering/step/stack-resource theorem. -/
theorem sourceTarget_reads {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (funds : ContractWorld.Address → Backend.Environment.Word) :
    (sourceMagicReads G F (n+1)).run s=
      (.ok (.val (uintValueOfWord E.layout G.timestamp),.val (Source.Val.address F.sender),
        .val (uintValueOfWord E.layout F.value)),s) ∧
    (uintValueOfWord E.layout G.timestamp).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .timestamp) ∧
    (Source.Val.address (D := E.layout) (p := false) F.sender).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .msgSender) ∧
    (uintValueOfWord E.layout F.value).word.map environmentWord=
      some (Backend.Environment.observe (sourceEnvironmentFrame G F funds) .msgValue) :=
  ⟨sourceMagic_sequence G F n s,sourceTarget_timestamp G F funds,sourceTarget_sender G F funds,sourceTarget_value G F funds⟩

end Solidity.Yul.Views
