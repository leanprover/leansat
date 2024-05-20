import LeanSAT.AIG.LawfulOperator
import LeanSAT.AIG.CachedGatesLemmas

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α] {aig : AIG α}

namespace RefStream

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

def append (lhs : RefStream aig lw) (rhs : RefStream aig rw) : RefStream aig (lw + rw) :=
  let ⟨lrefs, hl1, hl2⟩ := lhs
  let ⟨rrefs, hr1, hr2⟩ := rhs
  ⟨
    lrefs ++ rrefs,
    by simp [Array.size_append, hl1, hr1],
    by
      intro i h
      by_cases hsplit : i < lrefs.size
      . rw [Array.get_append_left]
        apply hl2
        omega
      . rw [Array.get_append_right]
        . apply hr2
          omega
        . omega
  ⟩

theorem getRef_append (lhs : RefStream aig lw) (rhs : RefStream aig rw) (idx : Nat) (hidx : idx < lw + rw)
    : (lhs.append rhs).getRef idx hidx
        =
      if h:idx < lw then
        lhs.getRef idx h
      else
        rhs.getRef (idx - lw) (by omega) := by
  simp only [getRef, append]
  split
  . simp [Ref.mk.injEq]
    rw [Array.get_append_left]
  . simp only [Ref.mk.injEq]
    rw [Array.get_append_right]
    . simp [lhs.hlen]
    . rw [lhs.hlen]
      omega

@[inline]
def getRefD (s : RefStream aig len) (idx : Nat) (alt : Ref aig) : Ref aig :=
  if hidx:idx < len then
    s.getRef idx hidx
  else
    alt

theorem getRef_in_bound (s : RefStream aig len) (idx : Nat) (alt : Ref aig) (hidx : idx < len)
    : s.getRefD idx alt = s.getRef idx hidx := by
  unfold getRefD
  simp [hidx]

theorem getRef_out_bound (s : RefStream aig len) (idx : Nat) (alt : Ref aig) (hidx : len ≤ idx)
    : s.getRefD idx alt = alt := by
  unfold getRefD
  split
  . omega
  . rfl

end RefStream

-- TODO: ZipTarget can benefit from this I think?
structure BinaryRefStream (aig : AIG α) (len : Nat) where
  lhs : RefStream aig len
  rhs : RefStream aig len

namespace BinaryRefStream

@[inline]
def cast {aig1 aig2 : AIG α} (s : BinaryRefStream aig1 len)
    (h : aig1.decls.size ≤ aig2.decls.size)
    : BinaryRefStream aig2 len :=
  let ⟨lhs, rhs⟩ := s
  ⟨lhs.cast h, rhs.cast h⟩

@[simp]
theorem lhs_getRef_cast {aig1 aig2 : AIG α} (s : BinaryRefStream aig1 len) (idx : Nat) (hidx : idx < len)
      (hcast : aig1.decls.size ≤ aig2.decls.size)
    : (s.cast hcast).lhs.getRef idx hidx
        =
      (s.lhs.getRef idx hidx).cast hcast := by
  simp [cast]

@[simp]
theorem rhs_getRef_cast {aig1 aig2 : AIG α} (s : BinaryRefStream aig1 len) (idx : Nat) (hidx : idx < len)
      (hcast : aig1.decls.size ≤ aig2.decls.size)
    : (s.cast hcast).rhs.getRef idx hidx
        =
      (s.rhs.getRef idx hidx).cast hcast := by
  simp [cast]

end BinaryRefStream
end AIG

