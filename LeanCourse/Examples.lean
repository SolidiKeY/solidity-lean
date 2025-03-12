import LeanCourse.Memory
import LeanCourse.Storage
import LeanCourse.StorageToMemory

inductive IdType where
  | idA | idB | idAcc deriving DecidableEq

inductive ValueSelector where
  | balanceS | ageS deriving DecidableEq

inductive IdSelector where
  | accountS deriving DecidableEq

open IdType
open ValueSelector
open IdSelector

def MemT      := Memory Nat ValueSelector IdSelector IdType
def StorageT  := Value Nat ValueSelector IdSelector
def StateType := State Nat ValueSelector IdSelector IdType
def Selector  := ValueSelector ⊕ IdSelector
def IdTyp     := IdT  ValueSelector IdSelector IdType
def ValType   := ValT Nat ValueSelector IdSelector IdType

open Value
open Memory
open Sum

@[simp] def account : Selector := inr accountS
@[simp] def balance : Selector := inl balanceS

-- alice.account.balance = 10
@[simp] def stAlice : StorageT := store mtst account $ store mtst balance $ var 10
@[simp] def stBob   : StorageT := store mtst account $ store mtst balance $ var 20
-- idA = alice
@[simp] def memAlice (mem : MemT) := copySt mem idA stAlice

theorem readCopy (mem : MemT) : Memory.read (memAlice mem) ⟨idA, [account]⟩ balance = inl 10
 := by simp

@[simp] def memBob (mem : MemT) := copySt (memAlice mem) idB stBob
@[simp] def idAA (mem : MemT) := read (memBob mem) ⟨idA, []⟩ account
@[simp] def idBB (mem : MemT) := read (memBob mem) ⟨idB, []⟩ account

theorem readIdAA (mem : MemT) : idAA mem = inr ⟨idA, [account]⟩ := by simp
theorem readIdBB (mem : MemT) : idBB mem = inr ⟨idB, [account]⟩ := by simp

theorem readIdABalance (mem : MemT) : read (memBob mem) ⟨idA, [account]⟩ balance = inl 10  := by simp

theorem readIdBBalance (mem : MemT) : read (memBob mem) ⟨idB, [account]⟩ balance = inl 20  := by simp

-- acc.balance = n
@[simp] def stAcc (n : Nat) : StorageT := store mtst balance $ var n
-- idAcc = acc
@[simp] def memAcc (mem : MemT) (n : Nat) := copySt mem idAcc (stAcc n)

theorem readAcc (mem : MemT) (n : Nat) : read (memAcc mem n) ⟨idAcc, []⟩ balance = inl n := by simp
