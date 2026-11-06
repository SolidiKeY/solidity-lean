import Solidity.Yul.Views.RootDeclarationReads
import Solidity.Yul.Views.RootDeclarationMetadata

namespace Solidity.Yul.Views.Controls

def rootAmbiguousEnv : Source.Env := ⟨[
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none true "x" .none⟩,
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "x" .none⟩]⟩
def rootAmbiguousCertificate : RootDeclarations rootAmbiguousEnv [(rootName "x",.int rootU8)] :=
  .cons (.scalar (.int rootU8) (by decide)) .nil

theorem root_duplicate_banks_rejected :
    ordinaryRootNames rootAmbiguousEnv none false = [rootName "x"] ∧
    ordinaryRootNames rootAmbiguousEnv none true = [rootName "x"] ∧
    rootAmbiguousEnv.transientRoot (rootPath "x") = true ∧
    prepareRootDeclarations rootAmbiguousCertificate none false account 0 = .error .duplicateDeclarations := ⟨rfl,rfl,rfl,rfl⟩

def rootImmutableDuplicate : Source.Env := ⟨[
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none (some .immutable) none false "x" .none⟩,
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "x" .none⟩]⟩
def rootImmutableCertificate : RootDeclarations rootImmutableDuplicate [(rootName "x",.int rootU8)] := .cons (.scalar (.int rootU8) (by decide)) .nil

theorem root_immutable_duplicate_rejected : prepareRootDeclarations rootImmutableCertificate none false account 0 = .error .duplicateDeclarations := rfl

def rootMalformedDuplicate : Source.Env := ⟨[
  ⟨.stateVar,"x",none,true,.struct "Bad" (.structMember (.elem .bool) "flag") .nil⟩,
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "x" .none⟩]⟩
def rootMalformedCertificate : RootDeclarations rootMalformedDuplicate [(rootName "x",.int rootU8)] := .cons (.scalar (.int rootU8) (by decide)) .nil

theorem root_malformed_kind_duplicate_rejected :
    ordinaryRootNames rootMalformedDuplicate none false = [rootName "x"] ∧
    allScopeRootNames rootMalformedDuplicate none = [rootName "x",rootName "x"] ∧
    prepareRootDeclarations rootMalformedCertificate none false account 0 = .error .duplicateDeclarations := ⟨rfl,rfl,rfl⟩

def rootOtherScopeEnv : Source.Env := ⟨[
  ⟨.stateVar,"x",some "Other",true,.stateVar (.elem (.int false 8 (by decide))) none none none true "x" .none⟩,
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "x" .none⟩]⟩
def rootOtherScopeCertificate : RootDeclarations rootOtherScopeEnv [(rootName "x",.int rootU8)] := .cons (.scalar (.int rootU8) (by decide)) .nil

theorem root_other_scope_does_not_alias : (prepareRootDeclarations rootOtherScopeCertificate none false account 0).toOption.isSome := by decide

def rootUnsupportedEnv : Source.Env := ⟨[
  ⟨.stateVar,"x",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "x" .none⟩,
  ⟨.stateVar,"unhandled",none,true,.stateVar (.elem .string) none none none false "unhandled" .none⟩]⟩
def rootIncompleteCertificate : RootDeclarations rootUnsupportedEnv [(rootName "x",.int rootU8)] := .cons (.scalar (.int rootU8) (by decide)) .nil

theorem root_unsupported_not_silently_skipped :
    ordinaryRootNames rootUnsupportedEnv none false = [rootName "x",rootName "unhandled"] ∧
    prepareRootDeclarations rootIncompleteCertificate none false account 0 = .error .metadataOrder := ⟨rfl,rfl⟩

theorem root_every_persistent_leaf_bank (c : ScalarPath rootEnv.layout (rootEnv.lay account))
    (member : c ∈ rootChecked.registrations) : rootEnv.transientRoot c.path = false := rootChecked.bank_agreement c member

theorem root_every_transient_leaf_bank (c : ScalarPath rootEnv.layout (rootEnv.lay account))
    (member : c ∈ rootTempChecked.registrations) : rootEnv.transientRoot c.path = true := rootTempChecked.bank_agreement c member

end Solidity.Yul.Views.Controls
