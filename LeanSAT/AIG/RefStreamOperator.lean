import LeanSAT.AIG.RefStream
import LeanSAT.AIG.LawfulStreamOperator

namespace AIG
namespace  RefStream

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α] {aig : AIG α}


structure MapTarget (aig : AIG α) (len : Nat) where
  stream : RefStream aig len
  func : (aig : AIG α) → Ref aig → Entrypoint α
  [lawful : LawfulOperator α Ref func]

attribute [instance] MapTarget.lawful

@[specialize]
def map (aig : AIG α) (target : MapTarget aig len) : RefStreamEntry α len :=
  go aig target.stream 0 (by omega) target.func
where
  @[specialize]
  go {len : Nat} (aig : AIG α) (s : RefStream aig len) (idx : Nat) (hidx : idx ≤ len)
      (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f]
      : RefStreamEntry α len :=
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
        go newAig s (idx + 1) (by omega) f
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

-- TODO: figure out how to use function induction here
theorem map.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefStream aig len)
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f]
    : aig.decls.size ≤ (go aig s idx hidx f).1.decls.size := by
  unfold go
  split
  . next h =>
    dsimp
    refine Nat.le_trans ?_ (by apply map.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem map_le_size {aig : AIG α} (target : MapTarget aig len)
    : aig.decls.size ≤ (map aig target).1.decls.size := by
  unfold map
  apply map.go_le_size

theorem map.go_decl_eq? {aig : AIG α} (i) (hi)
    (s : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig s i hi f).1.decls[idx]? = aig.decls[idx]? := by
  intro idx hidx
  unfold go
  split
  . dsimp
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
    : ∀ (idx : Nat) (h1) (h2), (go aig s i hi f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := map.go_decl_eq? i hi s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem map_decl_eq {aig : AIG α} (target : MapTarget aig len)
    : ∀ idx (h1 : idx < aig.decls.size) (h2), (map aig target).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold map
  apply map.go_decl_eq

instance : LawfulStreamOperator α MapTarget map where
  le_size := by intros; apply map_le_size
  decl_eq := by intros; apply map_decl_eq

structure ZipTarget (aig : AIG α) (len : Nat) where
  lhs : RefStream aig len
  rhs : RefStream aig len
  func : (aig : AIG α) → BinaryInput aig → Entrypoint α
  [lawful : LawfulOperator α BinaryInput func]

attribute [instance] ZipTarget.lawful

@[specialize]
def zip (aig : AIG α) (target : ZipTarget aig len) : RefStreamEntry α len :=
  go aig 0 .empty (by omega) target.lhs target.rhs target.func
where
  @[specialize]
  go (aig : AIG α) (idx : Nat) (s : RefStream aig idx) (hidx : idx ≤ len) (lhs rhs : RefStream aig len)
     (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
      : RefStreamEntry α len :=
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
        go newAig (idx + 1) s (by omega) (lhs.cast this) (rhs.cast this) f
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

theorem zip.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefStream aig idx)
    (lhs rhs : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (go aig idx s hidx lhs rhs f).1.decls.size := by
  unfold go
  split
  . dsimp
    refine Nat.le_trans ?_ (by apply zip.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem zip_le_size {aig : AIG α} (target : ZipTarget aig len)
    : aig.decls.size ≤ (zip aig target).1.decls.size := by
  unfold zip
  apply zip.go_le_size

theorem zip.go_decl_eq? {aig : AIG α} (i) (hi) (lhs rhs : RefStream aig len)
    (s : RefStream aig i) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig i s hi lhs rhs f).1.decls[idx]? = aig.decls[idx]? := by
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
    : ∀ (idx : Nat) (h1) (h2), (go aig i s hi lhs rhs f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := zip.go_decl_eq? i hi lhs rhs s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem zip_decl_eq {aig : AIG α} (target : ZipTarget aig len)
    : ∀ idx (h1 : idx < aig.decls.size) (h2),
        (zip aig target).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold zip
  apply zip.go_decl_eq

instance : LawfulStreamOperator α ZipTarget zip where
  le_size := by intros; apply zip_le_size
  decl_eq := by intros; apply zip_decl_eq

structure FoldTarget (aig : AIG α) where
  {len : Nat}
  stream : RefStream aig len
  func : (aig : AIG α) → BinaryInput aig → Entrypoint α
  [lawful : LawfulOperator α BinaryInput func]

attribute [instance] FoldTarget.lawful

@[inline]
def FoldTarget.mkAnd {aig : AIG α} (stream : RefStream aig length) : FoldTarget aig where
  stream := stream
  func := mkAndCached

@[specialize]
def fold (aig : AIG α) (target : FoldTarget aig) : Entrypoint α :=
  match haig:aig.mkConstCached true with
  | ⟨newAig, acc⟩ =>
    let input := target.stream.cast <| by
      intros
      have : newAig = (aig.mkConstCached true).aig := by rw [haig]
      rw [this]
      apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
      assumption
    go newAig acc 0 target.len input target.func
where
  @[specialize]
  go (aig : AIG α) (acc : Ref aig) (idx : Nat) (len : Nat) (input : RefStream aig len)
     (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
  : Entrypoint α :=
    if hidx:idx < len then
      match haig:f aig ⟨acc, input.getRef idx hidx⟩ with
      | ⟨newAig, newAcc⟩ =>
        let input := input.cast <| by
          intros
          have : newAig = (f aig ⟨acc, input.getRef idx hidx⟩).aig := by rw [haig]
          simp [this]
          apply LawfulOperator.lt_size_of_lt_aig_size (f := f)
          assumption
        go newAig newAcc (idx + 1) len input f
    else
      ⟨aig, acc⟩
  termination_by len - idx

-- TODO: figure out how to use function induction here
theorem fold.go_le_size {aig : AIG α} (acc : Ref aig) (idx : Nat) (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : aig.decls.size ≤ (go aig acc idx len s f).1.decls.size := by
  unfold go
  split
  . next h =>
    dsimp
    refine Nat.le_trans ?_ (by apply fold.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem fold_le_size {aig : AIG α} (target : FoldTarget aig)
    : aig.decls.size ≤ (fold aig target).1.decls.size := by
  unfold fold
  dsimp
  refine Nat.le_trans ?_ (by apply fold.go_le_size)
  apply LawfulOperator.le_size (f := mkConstCached)

theorem fold.go_decl_eq? {aig : AIG α} (acc : Ref aig) (i : Nat) (s : RefStream aig len)
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig acc i len s f).1.decls[idx]? = aig.decls[idx]? := by
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
        (go aig acc i len s f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := fold.go_decl_eq? acc i s f idx h1
  rw [Array.getElem?_lt, Array.getElem?_lt] at this
  injection this

theorem fold_decl_eq {aig : AIG α} (target : FoldTarget aig)
    : ∀ idx (h1 : idx < aig.decls.size) (h2), (fold aig target).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intros
  unfold fold
  dsimp
  rw [fold.go_decl_eq]
  rw [LawfulOperator.decl_eq (f := mkConstCached)]
  apply LawfulOperator.lt_size_of_lt_aig_size (f := mkConstCached)
  assumption

instance : LawfulOperator α FoldTarget fold where
  le_size := by intros; apply fold_le_size
  decl_eq := by intros; apply fold_decl_eq

@[simp]
theorem denote_map {aig : AIG α} (target : MapTarget aig len)
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(map aig target).1, (map aig target).2.getRef idx hidx, assign⟧
          =
        ⟦target.func aig (target.stream.getRef idx hidx), assign⟧ :=
  sorry

@[simp]
theorem denote_zip {aig : AIG α} (target : ZipTarget aig len)
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(zip aig target).1, (zip aig target).2.getRef idx hidx, assign⟧
          =
        ⟦target.func aig ⟨target.lhs.getRef idx hidx, target.rhs.getRef idx hidx⟩, assign⟧ :=
  sorry

@[simp]
theorem denote_fold_and {aig : AIG α} (s : RefStream aig len)
    : ⟦(fold aig (FoldTarget.mkAnd s)), assign⟧
        ↔
      (∀ (idx : Nat) (hidx : idx < len), ⟦aig, s.getRef idx hidx, assign⟧)
     :=
  sorry

end  RefStream
end AIG
