import LeanSAT.AIG.RefStream
import LeanSAT.AIG.LawfulStreamOperator

namespace AIG
namespace  RefStream

variable {α : Type} [BEq α] [Hashable α] [DecidableEq α] {aig : AIG α}

class LawfulMapOperator (α : Type) [BEq α] [Hashable α] [DecidableEq α]
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f] : Prop
  where
  chainable : ∀ (aig : AIG α) (input1 input2 : Ref aig) (h) (assign),
                ⟦f (f aig input1).aig (input2.cast h), assign⟧
                  =
                ⟦f aig input2, assign⟧

namespace LawfulMapOperator

@[simp]
theorem denote_prefix_cast_ref {aig : AIG α} {input1 input2 : Ref aig}
    {f : (aig : AIG α) → Ref aig → Entrypoint α}
    [LawfulOperator α Ref f] [LawfulMapOperator α f] {h}
      :
    ⟦f (f aig input1).aig (input2.cast h), assign⟧
      =
    ⟦f aig input2, assign⟧ := by
  rw [LawfulMapOperator.chainable]

instance : LawfulMapOperator α mkNotCached where
  chainable := by
    intros
    simp only [Ref_cast', denote_mkNotCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkNotCached)]

end LawfulMapOperator

class LawfulZipOperator (α : Type) [BEq α] [Hashable α] [DecidableEq α]
    (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f] : Prop
  where
  chainable : ∀ (aig : AIG α) (input1 input2 : BinaryInput aig) (h) (assign),
                ⟦f (f aig input1).aig (input2.cast h), assign⟧
                  =
                ⟦f aig input2, assign⟧

namespace LawfulZipOperator

@[simp]
theorem denote_prefix_cast_ref {aig : AIG α} {input1 input2 : BinaryInput aig}
    {f : (aig : AIG α) → BinaryInput aig → Entrypoint α}
    [LawfulOperator α BinaryInput f] [LawfulZipOperator α f] {h}
      :
    ⟦f (f aig input1).aig (input2.cast h), assign⟧
      =
    ⟦f aig input2, assign⟧ := by
  rw [LawfulZipOperator.chainable]

instance : LawfulZipOperator α mkAndCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref_cast', denote_mkAndCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkAndCached)]

instance : LawfulZipOperator α mkOrCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref_cast', denote_mkOrCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkOrCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkOrCached)]

instance : LawfulZipOperator α mkXorCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref_cast', denote_mkXorCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkXorCached)]

instance : LawfulZipOperator α mkBEqCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref_cast', denote_mkBEqCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkBEqCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkBEqCached)]

instance : LawfulZipOperator α mkImpCached where
  chainable := by
    intros
    simp only [BinaryInput.cast, Ref_cast', denote_mkImpCached]
    rw [LawfulOperator.denote_mem_prefix (f := mkImpCached)]
    rw [LawfulOperator.denote_mem_prefix (f := mkImpCached)]

end LawfulZipOperator

structure MapTarget (aig : AIG α) (len : Nat) where
  stream : RefStream aig len
  func : (aig : AIG α) → Ref aig → Entrypoint α
  [lawful : LawfulOperator α Ref func]
  [chainable : LawfulMapOperator α func]

attribute [instance] MapTarget.lawful
attribute [instance] MapTarget.chainable

@[specialize]
def map (aig : AIG α) (target : MapTarget aig len) : RefStreamEntry α len :=
  go aig 0 (by omega) .empty target.stream target.func
where
  @[specialize]
  go {len : Nat} (aig : AIG α) (idx : Nat) (hidx : idx ≤ len) (s : RefStream aig idx) (input : RefStream aig len)
      (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f] [LawfulMapOperator α f]
      : RefStreamEntry α len :=
    if hidx:idx < len then
      match haig:f aig (input.getRef idx hidx) with
      | ⟨newAig, newRef⟩ =>
        have := by
          intros
          have : newAig = (f aig (input.getRef idx hidx)).aig := by rw [haig]
          rw [this]
          apply LawfulOperator.le_size_of_le_aig_size
          omega
        let input := input.cast this
        let s := s.cast this
        let s := s.pushRef newRef
        go newAig (idx + 1) (by omega) s input f
    else
      have : idx = len := by omega
      ⟨aig, this ▸ s⟩
  termination_by len - idx

theorem map.go_le_size {aig : AIG α} (idx : Nat) (hidx) (s : RefStream aig idx) (input : RefStream aig len)
    (f : (aig : AIG α) → Ref aig → Entrypoint α) [LawfulOperator α Ref f] [LawfulMapOperator α f]
    : aig.decls.size ≤ (go aig idx hidx s input f).aig.decls.size := by
  unfold go
  split
  . next h =>
    dsimp
    refine Nat.le_trans ?_ (by apply map.go_le_size)
    apply LawfulOperator.le_size
  . simp
  termination_by len - idx

theorem map_le_size {aig : AIG α} (target : MapTarget aig len)
    : aig.decls.size ≤ (map aig target).aig.decls.size := by
  unfold map
  apply map.go_le_size

theorem map.go_decl_eq? {aig : AIG α} (i) (hi)
    (s : RefStream aig i) (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f]
    : ∀ (idx : Nat) (_hidx : idx < aig.decls.size),
        (go aig i hi s input f).1.decls[idx]? = aig.decls[idx]? := by
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
    (s : RefStream aig i) (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f]
    : ∀ (idx : Nat) (h1) (h2), (go aig i hi s input f).1.decls[idx]'h2 = aig.decls[idx]'h1 := by
  intro idx h1 h2
  have := map.go_decl_eq? i hi s input f idx h1
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
  [chainable : LawfulZipOperator α func]

attribute [instance] ZipTarget.lawful
attribute [instance] ZipTarget.chainable

@[specialize]
def zip (aig : AIG α) (target : ZipTarget aig len) : RefStreamEntry α len :=
  go aig 0 .empty (by omega) target.lhs target.rhs target.func
where
  @[specialize]
  go (aig : AIG α) (idx : Nat) (s : RefStream aig idx) (hidx : idx ≤ len) (lhs rhs : RefStream aig len)
     (f : (aig : AIG α) → BinaryInput aig → Entrypoint α) [LawfulOperator α BinaryInput f]
      [chainable : LawfulZipOperator α f]
      : RefStreamEntry α len :=
    if hidx:idx < len then
      match haig:f aig ⟨lhs.getRef idx hidx, rhs.getRef idx hidx⟩ with
      | ⟨newAig, newRef⟩ =>
        have := by
          intros
          have : newAig = (f aig ⟨lhs.getRef idx hidx, rhs.getRef idx hidx⟩).aig := by rw [haig]
          rw [this]
          apply LawfulOperator.le_size_of_le_aig_size
          omega
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
    [chainable : LawfulZipOperator α f]
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
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
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
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
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
      apply LawfulOperator.le_size_of_le_aig_size (f := mkConstCached)
      omega
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
          rw [this]
          apply LawfulOperator.le_size_of_le_aig_size (f := f)
          omega
        go newAig newAcc (idx + 1) len input f
    else
      ⟨aig, acc⟩
  termination_by len - idx

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

namespace map

theorem go_getRef_aux {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
    (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
    [LawfulOperator α Ref f] [LawfulMapOperator α f]
    -- The hfoo here is a trick to make the dependent type gods happy
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig curr hcurr s input f).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr hcurr s input f = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro hfoo
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by len - curr

theorem go_getRef {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
      [LawfulOperator α Ref f] [LawfulMapOperator α f]
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig curr hcurr s input f).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
      [LawfulOperator α Ref f] [LawfulMapOperator α f] (start : Nat) (hstart)
  : ⟦
      (go aig curr hcurr s input f).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem denote_go {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (input : RefStream aig len) (f : (aig : AIG α) → Ref aig → Entrypoint α)
      [LawfulOperator α Ref f] [LawfulMapOperator α f]
    : ∀ (idx : Nat) (hidx1 : idx < len) (hidx2 : curr ≤ idx),
        ⟦(go aig curr hcurr s input f).aig, (go aig curr hcurr s input f).stream.getRef idx hidx1, assign⟧
          =
        ⟦f aig (input.getRef idx hidx1), assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr hcurr s input f = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . simp only [← heq]
        rw [go_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
      . rw [heq]
    | inr hlt =>
      rw [← hgo]
      rw [denote_go]
      . simp [getRef_cast, -Ref_cast']
      . omega
  . omega
termination_by len - curr

end map

@[simp]
theorem denote_map {aig : AIG α} (target : MapTarget aig len)
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(map aig target).aig, (map aig target).stream.getRef idx hidx, assign⟧
          =
        ⟦target.func aig (target.stream.getRef idx hidx), assign⟧ := by
  intro idx hidx
  unfold map
  apply map.denote_go
  omega

namespace zip

theorem go_getRef_aux {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
    (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
    [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
    -- The hfoo here is a trick to make the dependent type gods happy
    : ∀ (idx : Nat) (hidx : idx < curr) (hfoo),
        (go aig curr s hcurr lhs rhs f).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast hfoo := by
  intro idx hidx
  generalize hgo : go aig curr s hcurr lhs rhs f = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    intro hfoo
    rw [go_getRef_aux]
    rw [AIG.RefStream.getRef_push_ref_lt]
    . simp only [Ref.cast, Ref.mk.injEq]
      rw [AIG.RefStream.getRef_cast]
      . simp
      . assumption
    . apply go_le_size
  . dsimp at hgo
    rw [← hgo]
    simp only [Nat.le_refl, getRef, Ref_cast', Ref.mk.injEq, true_implies]
    congr
    . omega
    . simp
termination_by len - curr

theorem go_getRef {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
      [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
    : ∀ (idx : Nat) (hidx : idx < curr),
        (go aig curr s hcurr lhs rhs f).stream.getRef idx (by omega)
          =
        (s.getRef idx hidx).cast (by apply go_le_size) := by
  intros
  apply go_getRef_aux

theorem go_denote_mem_prefix {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
      [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
      (start : Nat) (hstart)
  : ⟦
      (go aig curr s hcurr lhs rhs f).aig,
      ⟨start, by apply Nat.lt_of_lt_of_le; exact hstart; apply go_le_size⟩,
      assign
    ⟧
      =
    ⟦aig, ⟨start, hstart⟩, assign⟧ := by
  apply denote.eq_of_aig_eq (entry := ⟨aig, start,hstart⟩)
  apply IsPrefix.of
  . intros
    apply go_decl_eq
  . intros
    apply go_le_size

theorem denote_go {aig : AIG α} (curr : Nat) (hcurr : curr ≤ len) (s : RefStream aig curr)
      (lhs rhs : RefStream aig len) (f : (aig : AIG α) → BinaryInput aig → Entrypoint α)
      [LawfulOperator α BinaryInput f] [chainable : LawfulZipOperator α f]
    : ∀ (idx : Nat) (hidx1 : idx < len) (hidx2 : curr ≤ idx),
        ⟦
          (go aig curr s hcurr lhs rhs f).aig,
          (go aig curr s hcurr lhs rhs f).stream.getRef idx hidx1,
          assign
        ⟧
          =
        ⟦f aig ⟨lhs.getRef idx hidx1, rhs.getRef idx hidx1⟩, assign⟧ := by
  intro idx hidx1 hidx2
  generalize hgo : go aig curr s hcurr lhs rhs f = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    cases Nat.eq_or_lt_of_le hidx2 with
    | inl heq =>
      rw [← hgo]
      rw [go_getRef]
      rw [AIG.RefStream.getRef_push_ref_eq']
      . simp only [← heq]
        rw [go_denote_mem_prefix]
        . simp
        . simp [Ref.hgate]
      . rw [heq]
    | inr hlt =>
      rw [← hgo]
      rw [denote_go]
      . simp [-Ref_cast']
      . omega
  . omega
termination_by len - curr

end zip

@[simp]
theorem denote_zip {aig : AIG α} (target : ZipTarget aig len)
    : ∀ (idx : Nat) (hidx : idx < len),
        ⟦(zip aig target).aig, (zip aig target).stream.getRef idx hidx, assign⟧
          =
        ⟦target.func aig ⟨target.lhs.getRef idx hidx, target.rhs.getRef idx hidx⟩, assign⟧ := by
  intros
  apply zip.denote_go
  omega

theorem fold.denote_go_and {aig : AIG α} (acc : AIG.Ref aig) (curr : Nat) (hcurr : curr ≤ len)
      (input : RefStream aig len)
    : ⟦
        (go aig acc curr len input mkAndCached).aig,
        (go aig acc curr len input mkAndCached).ref,
        assign
      ⟧
        =
      (
        ⟦aig, acc, assign⟧
          ∧
        (∀ (idx : Nat) (hidx1 : idx < len) (hidx2 : curr ≤ idx), ⟦aig, input.getRef idx hidx1, assign⟧)
      ):= by
  generalize hgo : go aig acc curr len input mkAndCached = res
  unfold go at hgo
  split at hgo
  . dsimp at hgo
    rw [← hgo]
    rw [denote_go_and]
    . simp only [denote_projected_entry, denote_mkAndCached, Bool.and_eq_true, getRef_cast,
        eq_iff_iff]
      constructor
      . intro h
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        constructor
        . assumption
        . intro idx hidx1 hidx2
          cases Nat.eq_or_lt_of_le hidx2 with
          | inl heq => simpa [heq] using h2
          | inr hlt =>
            specialize h3 idx hidx1 (by omega)
            rw [← h3]
            rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkAndCached)]
            . simp
            . simp [Ref.hgate]
      . simp only [and_imp]
        intro hacc hrest
        constructor
        . simp [hacc, hrest]
        . intro idx hidx1 hidx2
          specialize hrest idx hidx1 (by omega)
          rw [← hrest]
          rw [AIG.LawfulOperator.denote_mem_prefix (f := AIG.mkAndCached)]
          . simp
          . simp [Ref.hgate]
    . omega
  . rw [← hgo]
    simp only [eq_iff_iff, iff_self_and]
    omega
termination_by len - curr


@[simp]
theorem denote_fold_and {aig : AIG α} (s : RefStream aig len)
    : ⟦(fold aig (FoldTarget.mkAnd s)), assign⟧
        ↔
      (∀ (idx : Nat) (hidx : idx < len), ⟦aig, s.getRef idx hidx, assign⟧)
     := by
  unfold fold
  simp only [FoldTarget.mkAnd]
  rw [fold.denote_go_and]
  . simp only [denote_projected_entry, mkConstCached_eval_eq_mkConst_eval, denote_mkConst,
    Nat.zero_le, getRef_cast, Ref_cast', true_implies, true_and]
    constructor
    . intro h idx hidx
      specialize h idx hidx
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkConstCached)] at h
      rw [← h]
    . intro h idx hidx
      specialize h idx hidx
      rw [AIG.LawfulOperator.denote_mem_prefix (f := mkConstCached)]
      . simp only [← h]
      . apply RefStream.hrefs
        simp [FoldTarget.mkAnd, hidx]
  . omega

end  RefStream
end AIG
