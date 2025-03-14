import LeanCourse.StorageToMemory

inductive IdType where
  | idA | idB | idAcc deriving DecidableEq

inductive ValueSelector where
  | balanceS | ageS deriving DecidableEq

inductive valSelector where
  | accountS deriving DecidableEq

open IdType
open ValueSelector
open valSelector

def MemT      := Memory Nat ValueSelector valSelector IdType
def StorageT  := Value Nat ValueSelector valSelector
def StateType := State Nat ValueSelector valSelector IdType
def Selector  := FieldSelector ValueSelector valSelector
def IdTyp     := IdT  ValueSelector valSelector IdType
def ValSType  := ValT Nat ValueSelector valSelector IdType

variable (mem : MemT) (st : StorageT)

open Value
open Memory
open Sum

@[simp] def account : Selector := .idS  accountS
@[simp] def balance : Selector := .valS balanceS

-- alice.account.balance = 10
@[simp] def saveAlice : StorageT := save st [account, balance] $ var 10

theorem selectSaveAlice (isSt : isStruct st) : select (select (saveAlice st) account) balance = var 10 := by
  unfold saveAlice
  have h := selectSave st account [balance] (var 10) account (by aesop)
  rewrite [h]
  simp
  have h2 := selectSave (select st (FieldSelector.idS accountS))  balance [] (var 10) balance $ by aesop
  simp at h2
  rewrite [h2]
  simp

-- alice.account.balance = 10
@[simp] def stAlice : StorageT := store st account $ store mtst balance $ var 10
@[simp] def stBob   : StorageT := store st account $ store mtst balance $ var 20
-- idA = alice
@[simp] def memAlice (_ : isStruct st := by aesop) := copySt mem idA (stAlice st) $ by aesop


theorem readCopy (_ : isStruct st := by aesop) : Memory.read (memAlice mem st) ⟨idA, [account]⟩ balance = .val 10
 := by simp

@[simp] def memBob (_ : isStruct st := by aesop) := copySt (memAlice mem st) idB (stBob st) $ by aesop
@[simp] def idAA (_ : isStruct st := by aesop) := read (memBob mem st) ⟨idA, []⟩ account
@[simp] def idBB (_ : isStruct st := by aesop) := read (memBob mem st) ⟨idB, []⟩ account

theorem readIdAA (_ : isStruct st := by aesop) : idAA mem st = .id ⟨idA, [account]⟩ := by simp
theorem readIdBB (_ : isStruct st := by aesop) : idBB mem st = .id ⟨idB, [account]⟩ := by simp

theorem readIdABalance (_ : isStruct st := by aesop) : read (memBob mem st) ⟨idA, [account]⟩ balance
  = .val 10  := by
  unfold memBob
  have h2 := readSkip (memAlice mem st) idB idA (stBob st)
  rewrite [h2]
  clear h2
  unfold memAlice
  unfold copySt
  unfold stAlice
  unfold copyStAux
  simp

theorem readIdBBalance (_ : isStruct st := by aesop) : read (memBob mem st) ⟨idB, [account]⟩ balance = .val 20  := by simp

-- -- acc.balance = n
@[simp] def stAcc (n : Nat) : StorageT := store mtst balance $ var n
-- -- idAcc = acc
@[simp] def memAcc (mem : MemT) (n : Nat) := copySt mem idAcc (stAcc n)

theorem readAcc (mem : MemT) (n : Nat) : read (memAcc mem n) ⟨idAcc, []⟩ balance = .val n := by simp
