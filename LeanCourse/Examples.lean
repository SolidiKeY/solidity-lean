import LeanCourse.StorageToMemory

inductive IdTp where
  | idA | idB | idAcc deriving DecidableEq

inductive ValueSelector where
  | balanceS | ageS deriving DecidableEq

inductive valSelector where
  | accountS deriving DecidableEq

open IdTp
open ValueSelector
open valSelector

def MemT      := Memory Nat ValueSelector valSelector IdTp
def StorageT  := Value Nat ValueSelector valSelector
def StateType := State Nat ValueSelector valSelector IdTp
def Selector  := FieldSelector ValueSelector valSelector
def IdTyp     := IdT  ValueSelector valSelector IdTp
def ValSTp    := ValT Nat ValueSelector valSelector IdTp
def StructT   := Struct Nat ValueSelector valSelector

variable (mem : MemT) (st : StructT)

open Value
open Memory
open Sum

@[simp] def account : Selector := .idS  accountS
@[simp] def balance : Selector := .valS balanceS

-- alice.account.balance = 10
@[simp] def saveAlice : StorageT := save st.1 [account, balance] $ var 10

theorem selectSaveAlice : select (select (saveAlice st) account) balance = var 10 := by
  unfold saveAlice
  have h := selectSave st.1 account [balance] (var 10) account st.2
  rewrite [h]
  simp
  have _ := st.2
  have h2 := selectSave (select st.1 (FieldSelector.idS accountS))  balance [] (var 10) balance $ by aesop
  simp at h2
  rewrite [h2]
  simp

-- alice.account.balance = 10
@[simp] def stAlice : StorageT := store st.val account $ store mtst balance $ var 10
@[simp] def stBob   : StorageT := store st.val account $ store mtst balance $ var 20
-- idA = alice
@[simp] def memAlice := copySt mem idA (stAlice st) $ by have _ := st.2; aesop


theorem readCopy : Memory.read (memAlice mem st) ⟨idA, [account]⟩ balance = .val 10
 := by simp

@[simp] def memBob := copySt (memAlice mem st) idB (stBob st) $ by have _ := st.2; aesop
@[simp] def idAA := read (memBob mem st) ⟨idA, []⟩ account
@[simp] def idBB := read (memBob mem st) ⟨idB, []⟩ account

theorem readIdAA : idAA mem st = .id ⟨idA, [account]⟩ := by simp
theorem readIdBB : idBB mem st = .id ⟨idB, [account]⟩ := by simp

theorem readIdABalance : read (memBob mem st) ⟨idA, [account]⟩ balance
  = .val 10  := by
  unfold memBob
  have _ := st.2
  have h2 := readSkip (memAlice mem st) idB idA (stBob st)
  rewrite [h2]
  clear h2
  unfold memAlice
  unfold copySt
  unfold stAlice
  unfold copyStAux
  simp

theorem readIdBBalance : read (memBob mem st) ⟨idB, [account]⟩ balance = .val 20  := by simp

-- -- acc.balance = n
@[simp] def stAcc (n : Nat) : StorageT := store mtst balance $ var n
-- -- idAcc = acc
@[simp] def memAcc (mem : MemT) (n : Nat) := copySt mem idAcc (stAcc n)

theorem readAcc (mem : MemT) (n : Nat) : read (memAcc mem n) ⟨idAcc, []⟩ balance = .val n := by simp
