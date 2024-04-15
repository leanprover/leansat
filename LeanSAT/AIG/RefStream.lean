import LeanSAT.AIG.LawfulOperator
import LeanSAT.AIG.CachedGatesLemmas

namespace AIG

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α] {aig : AIG α}

structure RefStream (aig : AIG α) (length : Nat) where
  refs : Array Nat
  hlen : refs.size = length
  hrefs : ∀ (h : i < length), refs[i] < aig.decls.size

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
    (h : ∀ i, i < aig1.decls.size → i < aig2.decls.size)
    : RefStream aig2 len :=
  s.cast' <| by
    intro hall i hi
    apply h
    apply hall
    assumption

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

def map (aig : AIG α) (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] : (aig : AIG α) × RefStream aig len :=
  go aig s 0 (by omega)
where
  go (aig : AIG α) (s : RefStream aig len) (idx : Nat) (hidx : idx ≤ len)
      : (aig : AIG α) × RefStream aig len :=
    if hidx:idx < len then
      match haig:f aig (s.getRef idx hidx) with
      | ⟨newAig, newRef⟩ =>
        let s := s.cast <| by
          intros
          have : newAig = (f aig (s.getRef idx hidx)).aig := by rw [haig]
          rw [this]
          apply LawfulOperator.lt_size_of_lt_aig_size
          assumption
        let s := s.setRef newRef idx hidx
        go newAig s (idx + 1) (by omega)
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

-- TODO: figure out how to use function induction here
theorem map.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefStream aig len)
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f]
    : aig.decls.size ≤ (go f aig s idx hidx).1.decls.size := by
  unfold go
  split
  . next h =>
    dsimp
    refine Nat.le_trans ?_ (by apply map.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem map_le_size {aig : AIG α} (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : aig.decls.size ≤ (map aig s f).1.decls.size := by
  unfold map
  apply map.go_le_size

theorem map.go_decl_eq? {aig : AIG α} (i) (hi)
    (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go f aig s i hi).1.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . next h =>
    dsimp
    rw [map.go_decl_eq?]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    . rw [LawfulOperator.decl_eq]
      . apply LawfulOperator.lt_size_of_lt_aig_size
        assumption
      . assumption
    . apply LawfulOperator.lt_size_of_lt_aig_size
      assumption
  . simp
  termination_by len - i

theorem map.go_decl_eq {aig : AIG α} (i) (hi)
    (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : ∀ (idx : Nat) (h1) (h2), (go f aig s i hi).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := map.go_decl_eq? i hi s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem map_decl_eq {aig : AIG α} (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : ∀ idx (h1 : idx < aig.decls.size) (h2), (map aig s f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold map
  apply map.go_decl_eq

def zip (aig : AIG α) (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] : (aig : AIG α) × RefStream aig len :=
  go aig 0 .empty (by omega) lhs rhs
where
  go (aig : AIG α) (idx : Nat) (s : RefStream aig idx) (hidx : idx ≤ len) (lhs rhs : RefStream aig len)
      : (aig : AIG α) × RefStream aig len :=
    if hidx:idx < len then
      match haig:f aig ⟨lhs.getRef idx hidx, rhs.getRef idx hidx⟩ with
      | ⟨newAig, newRef⟩ =>
        have := by
          intros
          have : newAig = (f aig ⟨lhs.getRef idx hidx, rhs.getRef idx hidx⟩).aig := by rw [haig]
          rw [this]
          apply LawfulOperator.lt_size_of_lt_aig_size
          assumption
        let s := s.cast this
        let s := s.pushRef newRef
        go newAig (idx + 1) s (by omega) (lhs.cast this) (rhs.cast this)
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

theorem zip.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefStream aig idx)
    (lhs rhs : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (go f aig idx s hidx lhs rhs).1.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply zip.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem zip_le_size {aig : AIG α} (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (zip aig lhs rhs f).1.decls.size := by
  unfold zip
  apply zip.go_le_size

theorem zip.go_decl_eq? {aig : AIG α} (i) (hi) (lhs rhs : RefStream aig len)
    (s : RefStream aig i) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go f aig i s hi lhs rhs).1.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . next h =>
    dsimp
    rw [zip.go_decl_eq?]
    rw [Array.getElem?_lt, Array.getElem?_lt]
    . rw [LawfulOperator.decl_eq]
      . apply LawfulOperator.lt_size_of_lt_aig_size
        assumption
      . assumption
    . apply LawfulOperator.lt_size_of_lt_aig_size
      assumption
  . simp
  termination_by len - i

theorem zip.go_decl_eq {aig : AIG α} (i) (hi) (lhs rhs : RefStream aig len)
    (s : RefStream aig i) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (h1) (h2), (go f aig i s hi lhs rhs).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := zip.go_decl_eq? i hi lhs rhs s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem zip_decl_eq {aig : AIG α} (lhs rhs : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ idx (h1 : idx < aig.decls.size) (h2),
        (zip aig lhs rhs f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold zip
  apply zip.go_decl_eq

def fold (aig : AIG α) (input : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] : Entrypoint α :=
  match haig:aig.mkConstCached true with
  | ⟨newAig, acc⟩ =>
    let input := input.cast <| by
      intros
      have : newAig = (aig.mkConstCached true).aig := by rw [haig]
      rw [this]
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
      assumption
    go newAig acc 0 input
where
  go (aig : AIG α) (acc : Ref aig) (idx : Nat) (input : RefStream aig len) : Entrypoint α :=
    if hidx:idx < len then
      match haig:f aig ⟨acc, input.getRef idx hidx⟩ with
      | ⟨newAig, newAcc⟩ =>
        let input := input.cast <| by
          intros
          have : newAig = (f aig ⟨acc, input.getRef idx hidx⟩).aig := by rw [haig]
          rw [this]
          apply LawfulOperator.lt_size_of_lt_aig_size
          assumption
        go newAig newAcc (idx + 1) input
    else
      ⟨aig, acc⟩
  termination_by len - idx

-- TODO: figure out how to use function induction here
theorem fold.go_le_size {aig : AIG α} (acc : Ref aig) (idx : Nat) (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (go f aig acc idx s).1.decls.size := by
  unfold go
  split
  . next h =>
    dsimp
    refine Nat.le_trans ?_ (by apply fold.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem fold_le_size {aig : AIG α} (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (fold aig s f).1.decls.size := by
  unfold fold
  dsimp
  refine Nat.le_trans ?_ (by apply fold.go_le_size)
  apply LawfulOperator.le_size (f := mkConstCached)

theorem fold.go_decl_eq? {aig : AIG α} (acc : Ref aig) (i : Nat) (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go f aig acc i s).1.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . next h =>
    dsimp
    rw [fold.go_decl_eq?]
    . rw [Array.getElem?_lt, Array.getElem?_lt]
      rw [LawfulOperator.decl_eq]
      . apply LawfulOperator.lt_size_of_lt_aig_size
        assumption
      . assumption
    . apply LawfulOperator.lt_size_of_lt_aig_size
      assumption
  . simp
  termination_by len - i

theorem fold.go_decl_eq {aig : AIG α} (acc : Ref aig) (i : Nat) (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (h1) (h2),
        (go f aig acc i s).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := fold.go_decl_eq? acc i s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem fold_decl_eq {aig : AIG α} (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ idx (h1 : idx < aig.decls.size) (h2), (fold aig s f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold fold
  dsimp
  rw [fold.go_decl_eq]
  rw [LawfulOperator.decl_eq (f := mkConstCached)]
  apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
  assumption

-- TODO: denotational theory for map zip and fold
@[simp]
theorem denote_map {aig : AIG α} (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(map aig s f).1, (map aig s f).2.getRef idx hidx, assign⟧
          =
        ⟦f aig (s.getRef idx hidx), assign⟧ :=
  sorry

@[simp]
theorem denote_zip {aig : AIG α} (lhs rhs : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(zip aig lhs rhs f).1, (zip aig lhs rhs f).2.getRef idx hidx, assign⟧
          =
        ⟦f aig ⟨lhs.getRef idx hidx, rhs.getRef idx hidx⟩, assign⟧ :=
  sorry

@[simp]
theorem denote_fold_and {aig : AIG α} (s : RefStream aig len)
    : ⟦(fold aig s mkAndCached), assign⟧
        ↔
      (∀ (idx : Nat) (hidx : idx < len), ⟦aig, s.getRef idx hidx, assign⟧)
     :=
  sorry



end RefStream
end AIG

