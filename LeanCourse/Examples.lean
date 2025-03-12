import LeanCourse.Memory
import LeanCourse.Storage
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
def ValSType   := ValT Nat ValueSelector valSelector IdType

open Value
open Memory
open Sum

@[simp] def account : Selector := .idS  accountS
@[simp] def balance : Selector := .valS balanceS

-- alice.account.balance = 10
@[simp] def stAlice : StorageT := store mtst account $ store mtst balance $ var 10
@[simp] def stBob   : StorageT := store mtst account $ store mtst balance $ var 20
-- idA = alice
@[simp] def memAlice (mem : MemT) := copySt mem idA stAlice

theorem readCopy (mem : MemT) : Memory.read (memAlice mem) ⟨idA, [account]⟩ balance = .val 10
 := by simp

@[simp] def memBob (mem : MemT) := copySt (memAlice mem) idB stBob
@[simp] def idAA (mem : MemT) := read (memBob mem) ⟨idA, []⟩ account
@[simp] def idBB (mem : MemT) := read (memBob mem) ⟨idB, []⟩ account

theorem readIdAA (mem : MemT) : idAA mem = .id ⟨idA, [account]⟩ := by simp
theorem readIdBB (mem : MemT) : idBB mem = .id ⟨idB, [account]⟩ := by simp

theorem readIdABalance (mem : MemT) : read (memBob mem) ⟨idA, [account]⟩ balance = .val 10  := by simp

theorem readIdBBalance (mem : MemT) : read (memBob mem) ⟨idB, [account]⟩ balance = .val 20  := by simp

-- acc.balance = n
@[simp] def stAcc (n : Nat) : StorageT := store mtst balance $ var n
-- idAcc = acc
@[simp] def memAcc (mem : MemT) (n : Nat) := copySt mem idAcc (stAcc n)

theorem readAcc (mem : MemT) (n : Nat) : read (memAcc mem n) ⟨idAcc, []⟩ balance = .val n := by simp
