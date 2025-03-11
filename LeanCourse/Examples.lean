import LeanCourse.Memory
import LeanCourse.Storage
import LeanCourse.StorageToMemory

inductive IdType where
  | idA | idB deriving DecidableEq

inductive ValueSelector where
  | balanceS | ageS deriving DecidableEq

inductive IdSelector where
  | accountS deriving DecidableEq

open IdType
open ValueSelector
open IdSelector

def MemT := Memory Nat ValueSelector IdSelector IdType
def StorageT := Value Nat ValueSelector IdSelector
def StateType := State Nat ValueSelector IdSelector IdType
def Selector := ValueSelector ⊕ IdSelector
def IdTyp := IdT  ValueSelector IdSelector IdType
def ValType := ValT Nat ValueSelector IdSelector IdType

open Value
open Memory
open Sum

@[simp] def account : Selector := inr accountS
@[simp] def balance : Selector := inl balanceS

-- alice.account.balance = 10
@[simp] def stAlice : StorageT := store mtst account $ store mtst balance $ var 10
-- idA = alice
@[simp] def memAlice (mem : MemT) := copySt mem idA stAlice $ by simp

theorem readCopy (mem : MemT) : Memory.read (memAlice mem) ⟨idA, [account]⟩ balance = inl 10
 := by simp
