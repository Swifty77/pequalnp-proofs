import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_653_aux

-- Relabeling construction adapted from the project proof L_meta_542.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

private lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

private lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private def starGates (center left right k o : ℕ) : List Gate :=
  [⟨GateOp.or, [left, right]⟩, ⟨GateOp.and, [center, k]⟩,
    ⟨GateOp.or, [if o < k then o else k + 2, k + 1]⟩]

private lemma star_eval (w : List Bool) (a b c o : ℕ) (ha : a < w.length) :
    ((starGates a b c w.length o).foldl step w).getD (w.length + 2) false =
      (w.getD o false || (w.getD a false && (w.getD b false || w.getD c false))) := by
  let r := w.getD b false || w.getD c false
  let w₁ := w ++ [r]
  let t := w.getD a false && r
  let w₂ := w₁ ++ [t]
  have h₁ : w₁.length = w.length + 1 := by simp [w₁]
  have h₂ : w₂.length = w.length + 2 := by simp [w₂, h₁]
  have hread (j : ℕ) (hj : j < w.length) : w₂.getD j false = w.getD j false := by
    rw [show w₂ = w₁ ++ [t] from rfl, List.getD_append _ _ _ _ (by omega)]
    exact List.getD_append _ _ _ _ hj
  have ha₁ : w₁.getD a false = w.getD a false := List.getD_append _ _ _ _ ha
  have hr : w₁.getD w.length false = r := getD_snoc_eq _ _ _
  have ht : w₂.getD (w.length + 1) false = t := by rw [← h₁]; exact getD_snoc_eq _ _ _
  have ho : w₂.getD (if o < w.length then o else w.length + 2) false = w.getD o false := by
    by_cases h : o < w.length
    · simpa [h] using hread o h
    · rw [ite_eq_right h, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have e₁ : step w ⟨GateOp.or, [b, c]⟩ = w₁ := by simp [step, GateOp.eval, w₁, r]
  have e₂ : step w₁ ⟨GateOp.and, [a, w.length]⟩ = w₂ := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, ha₁, hr, w₂, t]
  simp only [starGates, List.foldl_cons, List.foldl_nil, e₁, e₂]
  simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  rw [← h₂, getD_snoc_eq, h₂, ho, ht]

private lemma addStar {m s : ℕ} {f : (Fin m → Bool) → Bool} (a b c : Fin m)
    (h : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || (x a && (x b || x c))) (s + 3) := by
  obtain ⟨C, hok, hsize, heval⟩ := h
  let k := m + C.gates.length
  refine ⟨⟨C.gates ++ starGates a.val b.val c.val k C.output, k + 2⟩, ?_, ?_, ?_⟩
  · intro gate hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hok gate hm
    · simp only [starGates, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> simp
  · simpa [Circuit.size, starGates] using Nat.add_le_add_right hsize 3
  · intro x
    let w := C.gates.foldl step (List.ofFn x)
    have hw : w.length = k := by simp [w, run_length, k]
    have hinput (i : Fin m) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        run_keep _ _ _ (by simp)]
      simp
    have ho : w.getD C.output false = f x := heval x
    change ((C.gates ++ starGates a.val b.val c.val k C.output).foldl step (List.ofFn x)).getD
      (k + 2) false = _
    rw [List.foldl_append]
    change ((starGates a.val b.val c.val k C.output).foldl step w).getD (k + 2) false = _
    rw [← hw, star_eval w _ _ _ _ (by have := a.isLt; omega), ho, hinput, hinput, hinput]

private def hits {m : ℕ} (x : Fin m → Bool) (star : Fin m × Fin m × Fin m) : Prop :=
  x star.1 = true ∧ (x star.2.1 = true ∨ x star.2.2 = true)

private def hitBool {m : ℕ} (x : Fin m → Bool) (star : Fin m × Fin m × Fin m) : Bool :=
  x star.1 && (x star.2.1 || x star.2.2)

private lemma decide_same (p : Prop) (d e : Decidable p) : @decide p d = @decide p e :=
  congrArg (fun d => @decide p d) (Subsingleton.elim d e)

private lemma addStars {m s : ℕ} {f : (Fin m → Bool) → Bool}
    (stars : List (Fin m × Fin m × Fin m)) (h : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f x || stars.any (hitBool x)) (3 * stars.length + s) := by
  induction stars with
  | nil => simpa using h
  | cons star rest ih =>
    have hh := addStar star.1 star.2.1 star.2.2 ih
    convert hh using 1
    · funext x
      simp [hitBool, Bool.or_left_comm, Bool.or_comm]
    · simp only [List.length_cons]; omega

private def path {m l : ℕ} (x : Fin m → Bool) (z : Fin l → Fin m) (u v : Fin m) : Prop :=
  ∃ i : Fin l, x (z i) = true ∧ ((i.val = 0 ∧ x u = true) ∨
    (i.val + 1 = l ∧ x v = true) ∨ ∃ j : Fin l, j.val = i.val + 1 ∧ x (z j) = true)

private lemma reverse_imp {m l : ℕ} (x : Fin m → Bool) (z : Fin l → Fin m) (u v : Fin m)
    (h : path x (fun i => z i.rev) v u) : path x z u v := by
  rcases h with ⟨i, hi, (⟨hi0, hv⟩ | ⟨hiLast, hu⟩ | ⟨j, hj, hjx⟩)⟩
  · exact ⟨i.rev, hi, Or.inr (Or.inl ⟨by simp [Fin.val_rev]; omega, hv⟩)⟩
  · exact ⟨i.rev, hi, Or.inl ⟨by simp [Fin.val_rev]; omega, hu⟩⟩
  · exact ⟨j.rev, hjx, Or.inr (Or.inr ⟨i.rev, by simp [Fin.val_rev]; omega, hi⟩)⟩

private lemma reverse_path {m l : ℕ} (x : Fin m → Bool) (z : Fin l → Fin m) (u v : Fin m) :
    path x (fun i => z i.rev) v u ↔ path x z u v := by
  refine ⟨reverse_imp x z u v, ?_⟩
  intro h
  exact reverse_imp x (fun i => z i.rev) v u (by simpa using h)

private def evenIdx {h : ℕ} (j : Fin h) : Fin (2 * h) := ⟨2 * j.val, by omega⟩

private def oddIdx {h : ℕ} (j : Fin h) : Fin (2 * h) := ⟨2 * j.val + 1, by omega⟩

private def rightNeighbor {m h : ℕ} (z : Fin (2 * h) → Fin m) (v : Fin m) (j : Fin h) : Fin m :=
  if hj : 2 * j.val + 2 < 2 * h then z ⟨2 * j.val + 2, hj⟩ else v

private def edgeStars {m h : ℕ} (z : Fin (2 * h) → Fin m) (v : Fin m) :
    List (Fin m × Fin m × Fin m) :=
  List.ofFn fun j : Fin h => (z (oddIdx j), z (evenIdx j), rightNeighbor z v j)

private lemma edgeStars_path {m h : ℕ} (hh : 1 ≤ h) (x : Fin m → Bool)
    (z : Fin (2 * h) → Fin m) (u v : Fin m) :
    (x u = true ∧ x (z ⟨0, by omega⟩) = true ∨ ∃ star ∈ edgeStars z v, hits x star) ↔
      path x z u v := by
  have intoStars (j : Fin h) (hj : hits x (z (oddIdx j), z (evenIdx j), rightNeighbor z v j)) :
      ∃ star ∈ edgeStars z v, hits x star :=
    ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  constructor
  · rintro (⟨hu, hz⟩ | ⟨star, hm, hs⟩)
    · exact ⟨⟨0, by omega⟩, hz, Or.inl ⟨rfl, hu⟩⟩
    · rcases List.mem_ofFn.mp hm with ⟨j, rfl⟩
      change x (z (oddIdx j)) = true ∧
        (x (z (evenIdx j)) = true ∨ x (rightNeighbor z v j) = true) at hs
      rcases hs with ⟨ho, he | hr⟩
      · exact ⟨evenIdx j, he, Or.inr (Or.inr ⟨oddIdx j, rfl, ho⟩)⟩
      · unfold rightNeighbor at hr
        split at hr
        · exact ⟨oddIdx j, ho, Or.inr (Or.inr ⟨_, by simp [oddIdx], hr⟩)⟩
        · exact ⟨oddIdx j, ho, Or.inr (Or.inl ⟨by simp [oddIdx]; omega, hr⟩)⟩
  · rintro ⟨i, hi, (⟨hi0, hu⟩ | ⟨hiLast, hv⟩ | ⟨j, hj, hjx⟩)⟩
    · have eq : i = (⟨0, by omega⟩ : Fin (2 * h)) := Fin.ext hi0
      exact Or.inl ⟨hu, by simpa [eq] using hi⟩
    · let t : Fin h := ⟨h - 1, by omega⟩
      have eq : oddIdx t = i := by apply Fin.ext; simp [oddIdx, t]; omega
      have hlast : ¬ 2 * t.val + 2 < 2 * h := by simp [t]; omega
      exact Or.inr (intoStars t ⟨by simpa [eq] using hi, Or.inr (by
        simpa [rightNeighbor, hlast] using hv)⟩)
    · let t : Fin h := ⟨i.val / 2, by omega⟩
      by_cases hei : 2 * t.val = i.val
      · have ei : evenIdx t = i := Fin.ext hei
        have ej : oddIdx t = j := by apply Fin.ext; simp [oddIdx]; omega
        exact Or.inr (intoStars t ⟨by simpa [ej] using hjx, Or.inl (by simpa [ei] using hi)⟩)
      · have ei : oddIdx t = i := by apply Fin.ext; simp [oddIdx, t] at *; omega
        have hn : 2 * t.val + 2 < 2 * h := by simp [t] at *; omega
        have ej : (⟨2 * t.val + 2, hn⟩ : Fin (2 * h)) = j := by
          apply Fin.ext
          change 2 * t.val + 2 = j.val
          have eq : 2 * t.val + 1 = i.val := congrArg Fin.val ei
          omega
        exact Or.inr (intoStars t ⟨by simpa [ei] using hi, Or.inr (by
          simpa [rightNeighbor, hn, ej] using hjx)⟩)

private lemma extendFront {N m h s : ℕ} (hh : 1 ≤ h) (base : Fin N → Fin m)
    (z : Fin (2 * h) → Fin m) (u v : Fin N) (g : (Fin N → Bool) → Bool)
    (H : HasCircuitSize (N + 1)
      (fun x => g (fun i => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s) :
    HasCircuitSize m
      (fun x => g (x ∘ base) || @decide (path x z (base u) (base v)) (Classical.propDecidable _))
      (3 * h + s) := by
  classical
  let π : Fin (N + 1) → Fin m := Fin.lastCases (z ⟨0, by omega⟩) base
  have H' : HasCircuitSize m (fun x => g (x ∘ base) || (x (base u) && x (z ⟨0, by omega⟩))) s := by
    simpa [π, Function.comp_def] using relabel_size π _ s H
  have hc := addStars (edgeStars z (base v)) H'
  have hlength : (edgeStars z (base v)).length = h := by simp [edgeStars]
  rw [hlength] at hc
  convert hc using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  have hstars : (edgeStars z (base v)).any (hitBool x) = true ↔
      ∃ star ∈ edgeStars z (base v), hits x star := by
    simp [List.any_eq_true, hits, hitBool]
  rw [hstars]
  rw [or_assoc, edgeStars_path hh]

end PEqualNP.Outside.L_meta_653_aux

open PEqualNP.Outside.L_meta_653_aux PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_653 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), 1 ≤ h → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g hh s
  let base : Fin N → Fin (N + 2 * h) := Fin.castAdd (2 * h)
  let z : Fin (2 * h) → Fin (N + 2 * h) := Fin.natAdd N
  constructor
  · intro H
    have hs := extendFront hh base z u v g H
    convert hs using 1
    funext x
    apply congrArg (fun b => g (x ∘ base) || b)
    exact decide_same (path x z (base u) (base v)) _ _
  · intro H
    have hs := extendFront hh base (fun i => z i.rev) v u g H
    convert hs using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, reverse_path]
    rfl
