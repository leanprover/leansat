import LeanSAT.AIG.LawfulOperator
import LeanSAT.AIG.CachedGatesLemmas

namespace AIG
namespace RefStream

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α] {aig : AIG α}

def empty : RefStream aig 0 where
  refs := #[]
  hlen := by simp
  hrefs := by intros; contradiction

@[inline]
def cast' {aig1 aig2 : AIG α} (s : RefStream aig1 len)
    (h :
      (∀ {i : Nat} (h : i < len), s.refs[i]'(by have := s.hlen; omega) < aig1.decls.size)
        → ∀ {i : Nat} (h : i < len), s.refs[i]'(by have := s.hlen; omega) < aig2.decls.size)
    : RefStream aig2 len :=
  { s with
      hrefs := by
        intros
        apply h
        · intros
          apply s.hrefs
          assumption
        · assumption
  }

@[inline]
def cast {aig1 aig2 : AIG α} (s : RefStream aig1 len)
    (h : aig1.decls.size ≤ aig2.decls.size)
    : RefStream aig2 len :=
  s.cast' <| by
    intro hall i hi
    specialize hall hi
    omega

@[inline]
def getRef (s : RefStream aig len) (idx : Nat) (hidx : idx < len) : Ref aig :=
  let ⟨refs, hlen, hrefs⟩ := s
  let ref := refs[idx]'(by rw [hlen]; assumption)
  ⟨ref, by apply hrefs; assumption⟩

@[inline]
def pushRef (s : RefStream aig len) (ref : AIG.Ref aig) : RefStream aig (len + 1) :=
  let ⟨refs, hlen, hrefs⟩ := s
  ⟨
    refs.push ref.gate,
    by simp [hlen],
    by
      intro i hi
      simp only [Array.get_push]
      split
      . apply hrefs
        omega
      . apply AIG.Ref.hgate
  ⟩

@[simp]
theorem getRef_push_ref_eq (s : RefStream aig len) (ref : AIG.Ref aig)
    : (s.pushRef ref).getRef len (by omega) = ref := by
  have := s.hlen
  simp [getRef, pushRef, ← this]

-- This variant exists because it is sometimes hard to rewrite properly with DTT
theorem getRef_push_ref_eq' (s : RefStream aig len) (ref : AIG.Ref aig) (idx : Nat) (hidx : idx = len)
    : (s.pushRef ref).getRef idx (by omega) = ref := by
  have := s.hlen
  simp [getRef, pushRef, ← this, hidx]

theorem getRef_push_ref_lt (s : RefStream aig len) (ref : AIG.Ref aig) (idx : Nat) (hidx : idx < len)
    : (s.pushRef ref).getRef idx (by omega) = s.getRef idx hidx := by
  simp [getRef, pushRef]
  cases ref
  simp only [Ref.mk.injEq]
  rw [Array.get_push_lt]

@[simp]
theorem getRef_cast {aig1 aig2 : AIG α} (s : RefStream aig1 len) (idx : Nat) (hidx : idx < len)
      (hcast : aig1.decls.size ≤ aig2.decls.size)
    : (s.cast hcast).getRef idx hidx
        =
      (s.getRef idx hidx).cast hcast := by
  simp [cast, cast', getRef]

@[inline]
def setRef (s : RefStream aig len) (ref : AIG.Ref aig) (idx : Nat) (hidx : idx < len)
    : RefStream aig len :=
  let ⟨refs, hlen, hrefs⟩ := s
  let refs := refs.set ⟨idx, by simp [hidx, hlen]⟩ ref.gate
  ⟨
    refs,
    by simp[refs, hlen],
    by
      intros
      simp only [Array.getElem_set, refs]
      split
      . apply Ref.hgate
      . apply hrefs
        assumption
  ⟩

end RefStream
end AIG

