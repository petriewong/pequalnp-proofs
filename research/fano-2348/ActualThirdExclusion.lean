import PEqualNP.Defs.TopForm

namespace ProofLantern.Remap

structure Gate where
  isOr : Bool
  left : Nat
  right : Nat

def applyGate (g : Gate) (a b : Bool) : Bool := if g.isOr then a || b else a && b

def value (g : Gate) (w : List Bool) : Bool :=
  applyGate g (w.getD g.left false) (w.getD g.right false)

def remap (mv : List Nat) (g : Gate) : Gate :=
  ⟨g.isOr, mv.getD g.left 0, mv.getD g.right 0⟩

def Agree (mv : List Nat) (old fresh : List Bool) : Prop :=
  mv.length = old.length ∧
  ∀ i < old.length, mv.getD i 0 < fresh.length ∧
    fresh.getD (mv.getD i 0) false = old.getD i false

private theorem getD_app {A : Type} (xs ys : List A) (i : Nat) (d : A)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left h]

private theorem getD_end {A : Type} (xs : List A) (a d : A) :
    (xs ++ [a]).getD xs.length d = a := by simp

private theorem append_agree (mv : List Nat) (old fresh : List Bool) (a : Nat) (v : Bool)
    (h : Agree mv old fresh) (ha : a < fresh.length) (hv : fresh.getD a false = v) :
    Agree (mv ++ [a]) (old ++ [v]) fresh := by
  refine ⟨by simp [h.1],?_⟩
  intro i hi
  by_cases t : i < old.length
  · rw [getD_app _ _ _ _ (by rw [h.1]; exact t),getD_app _ _ _ _ t]
    exact h.2 i t
  · have e : i = old.length := by simp at hi; omega
    subst i
    have o : (mv ++ [a]).getD old.length 0 = a := by rw [← h.1]; exact getD_end _ _ _
    rw [o,getD_end]
    exact ⟨ha,hv⟩

theorem delete_step (mv : List Nat) (old fresh : List Bool) (flag : Nat) (g : Gate)
    (h : Agree mv old fresh) (fa : flag < fresh.length)
    (eq : fresh.getD flag false = value g old) :
    Agree (mv ++ [flag]) (old ++ [value g old]) fresh :=
  append_agree mv old fresh flag (value g old) h fa eq

theorem keep_step (mv : List Nat) (old fresh : List Bool) (g : Gate)
    (h : Agree mv old fresh) (hl : g.left < old.length) (hr : g.right < old.length) :
    let translated := remap mv g
    translated.left < fresh.length ∧ translated.right < fresh.length ∧
      Agree (mv ++ [fresh.length]) (old ++ [value g old])
        (fresh ++ [value translated fresh]) := by
  obtain ⟨ha,eqA⟩ := h.2 g.left hl
  obtain ⟨hb,eqB⟩ := h.2 g.right hr
  have ev : value (remap mv g) fresh = value g old := by
    simp only [value,remap]
    rw [eqA,eqB]
    rfl
  refine ⟨ha,hb,?_⟩
  have h' : Agree mv old (fresh ++ [value (remap mv g) fresh]) := by
    refine ⟨h.1,?_⟩
    intro i hi
    obtain ⟨b,e⟩ := h.2 i hi
    refine ⟨by rw [List.length_append]; simp only [List.length_singleton]; omega,?_⟩
    rw [getD_app _ _ _ _ b,e]
  exact append_agree mv old _ fresh.length (value g old) h' (by simp) ((getD_end _ _ _).trans ev)


def rebuild (flag : Nat) : List (Gate × Bool) → Nat → List Nat → List Nat × List Gate
  | [], _, mv => (mv,[])
  | (g,drop)::gs, next, mv =>
    if drop then rebuild flag gs next (mv ++ [flag])
    else
      let tail := rebuild flag gs (next+1) (mv ++ [next])
      (tail.1,remap mv g :: tail.2)

def evaluate : List Gate → List Bool → List Bool
  | [], w => w
  | g::gs,w => evaluate gs (w ++ [value g w])

def executeOriginal : List (Gate × Bool) → List Bool → List Bool
  | [], w => w
  | (g,_)::gs,w => executeOriginal gs (w ++ [value g w])

def admissible (flagValue : Bool) : List (Gate × Bool) → List Bool → Prop
  | [], _ => True
  | (g,drop)::gs, w =>
    g.left < w.length ∧ g.right < w.length ∧
    (drop = true → value g w = flagValue) ∧ admissible flagValue gs (w ++ [value g w])

def backwards : List Gate → Nat → Prop
  | [], _ => True
  | g::gs,n => g.left < n ∧ g.right < n ∧ backwards gs (n+1)

theorem rebuild_count (flag n : Nat) (gs : List (Gate × Bool)) (mv : List Nat) :
    (rebuild flag gs n mv).2.length = (gs.filter (fun k => !k.2)).length := by
  induction gs generalizing n mv with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨g,d⟩ := g
    cases d <;> simp [rebuild,ih]

theorem rebuild_correct (flag : Nat) (gs : List (Gate × Bool))
    (mv : List Nat) (old fresh : List Bool) (h : Agree mv old fresh)
    (fr : flag < fresh.length) (good : admissible (fresh.getD flag false) gs old) :
    let t := rebuild flag gs fresh.length mv
    backwards t.2 fresh.length ∧
      Agree t.1 (executeOriginal gs old) (evaluate t.2 fresh) := by
  induction gs generalizing mv old fresh with
  | nil => exact ⟨trivial,h⟩
  | cons g gs ih =>
    obtain ⟨g,d⟩ := g
    obtain ⟨hl,hr,hv,hgood⟩ := good
    cases d
    · obtain ⟨lu,ru,ha⟩ := keep_step mv old fresh g h hl hr
      let fresh' := fresh ++ [value (remap mv g) fresh]
      have fs : fresh'.length = fresh.length+1 := by simp [fresh']
      have fl : flag < fresh'.length := by rw [fs]; omega
      have gv : fresh'.getD flag false = fresh.getD flag false := getD_app _ _ _ _ fr
      have hh := ih (mv ++ [fresh.length]) (old ++ [value g old]) fresh' ha fl (by simpa only [gv] using hgood)
      dsimp only at hh
      rw [fs] at hh
      exact ⟨⟨lu,ru,hh.1⟩,hh.2⟩
    · have hh := delete_step mv old fresh flag g h fr (hv rfl).symm
      exact ih (mv ++ [flag]) (old ++ [value g old]) fresh hh fr hgood


theorem rebuild_count_exact (flag n k : Nat) (gs : List (Gate × Bool)) (mv : List Nat) :
    k + (rebuild flag gs n mv).2.length + (gs.filter Prod.snd).length = k + gs.length := by
  rw [rebuild_count]
  have h : (gs.filter (fun g => !g.2)).length + (gs.filter Prod.snd).length = gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      obtain ⟨g,b⟩ := g
      cases b <;> simp at * <;> omega
  omega

theorem rebuild_output (flag : Nat) (gs : List (Gate × Bool))
    (mv : List Nat) (old fresh : List Bool) (h : Agree mv old fresh)
    (fr : flag < fresh.length) (good : admissible (fresh.getD flag false) gs old)
    (output : Nat) (ho : output < (executeOriginal gs old).length) :
    let r := rebuild flag gs fresh.length mv
    (evaluate r.2 fresh).getD (r.1.getD output 0) false =
      (executeOriginal gs old).getD output false :=
  (rebuild_correct flag gs mv old fresh h fr good).2.2 output ho |>.2

end ProofLantern.Remap


namespace ProofLantern.Remap.Upstream

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def pack (g : Remap.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨if g.isOr then GateOp.or else GateOp.and,[g.left,g.right]⟩

def circuit (gs : List Remap.Gate) (out : Nat) : Circuit :=
  ⟨gs.map pack,out⟩

theorem pack_eval (g : Remap.Gate) (w : List Bool) :
    (pack g).op.eval ((pack g).inputs.map fun i => w.getD i false) =
       Remap.value g w := by
  obtain ⟨o,a,b⟩ := g
  cases o <;> simp [pack,GateOp.eval,Remap.value,Remap.applyGate]

theorem wires (gs : List Remap.Gate) (out : Nat) (w : List Bool) :
    (circuit gs out).wires w = evaluate gs w := by
  change (gs.map pack).foldl (fun w g => w ++
    [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = _
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons,List.foldl_cons,pack_eval]
    exact ih _

private theorem backwards_at (gs : List Remap.Gate) (n : Nat) (j : Nat)
    (hj : j < gs.length) (h : backwards gs n) :
    gs[j].left < n+j ∧ gs[j].right < n+j := by
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => exact ⟨h.1,h.2.1⟩
    | succ j =>
      have h' := ih (n+1) j (by simp at hj; omega) h.2.2
      have eq : n+1+j = n+(j+1) := by omega
      rw [eq] at h'
      exact h'

theorem topology (gs : List Remap.Gate) (out n : Nat) (h : backwards gs n) :
    IsAO2 n (circuit gs out) := by
  refine ⟨?_,?_,?_⟩
  · intro g mem
    obtain ⟨orig,_,rfl⟩ := List.mem_map.mp mem
    unfold pack
    split <;> simp
  · intro j hj i read
    have hh : j < gs.length := by simpa [circuit] using hj
    have ha := backwards_at gs n j hh h
    unfold gateAt at read
    rw [List.getD_eq_getElem _ _ hj] at read
    have rr : (circuit gs out).gates[j] = pack gs[j] := by simp [circuit]
    rw [rr] at read
    simp [pack] at read
    rcases read with e | e
    · simpa [e] using ha.1
    · simpa [e] using ha.2
  · intro g mem
    obtain ⟨orig,_,rfl⟩ := List.mem_map.mp mem
    rfl

theorem original_wires (gs : List (Remap.Gate × Bool)) (out : Nat) (w : List Bool) :
    (circuit (gs.map Prod.fst) out).wires w = executeOriginal gs w := by
  rw [wires]
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨g,drop⟩
    exact ih _

/-- The generic remap preserves the actual repository's ordinary evaluated
output and emits an actual strict-backward binary AND/OR circuit. -/
theorem remap_actual (flag out : Nat) (gs : List (Remap.Gate × Bool))
    (mv : List Nat) (old fresh : List Bool) (h : Agree mv old fresh)
    (fr : flag < fresh.length) (valid : admissible (fresh.getD flag false) gs old)
    (ho : out < (executeOriginal gs old).length) :
    let r := rebuild flag gs fresh.length mv
    let result := circuit r.2 (r.1.getD out 0)
    IsAO2 fresh.length result ∧
      result.size + (gs.filter Prod.snd).length = gs.length ∧
      result.eval fresh = (circuit (gs.map Prod.fst) out).eval old := by
  let r := rebuild flag gs fresh.length mv
  refine ⟨topology r.2 _ _ (rebuild_correct _ _ _ _ _ h fr valid).1,?_,?_⟩
  · have hc := rebuild_count_exact flag fresh.length 0 gs mv
    simpa [Circuit.size,circuit] using hc
  · change (circuit r.2 (r.1.getD out 0)).eval fresh = _
    unfold Circuit.eval
    rw [wires,original_wires]
    exact rebuild_output _ _ _ _ _ h fr valid out ho


theorem evaluate_length (gs : List Remap.Gate) (x : List Bool) :
    (evaluate gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evaluate]
  | cons g gs ih =>
    rw [evaluate,ih]
    simp
    omega

theorem evaluate_append (pref tail : List Remap.Gate) (x : List Bool) :
    evaluate (pref ++ tail) x = evaluate tail (evaluate pref x) := by
  induction pref generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem backwards_append (pref tail : List Remap.Gate) (n : Nat)
    (hPrefix : backwards pref n) (hTail : backwards tail (n+pref.length)) :
    backwards (pref++tail) n := by
  induction pref generalizing n with
  | nil => simpa using hTail
  | cons g gs ih =>
    have t : backwards tail ((n+1)+gs.length) := by
      have eq : n + (g::gs).length = n+1+gs.length := by simp; omega
      rw [←eq]; exact hTail
    exact ⟨hPrefix.1,hPrefix.2.1,ih (n+1) hPrefix.2.2 t⟩

/-- Package pref and rebuilt suffix as one actual upstream circuit. The
compiled circuit's gate list and wire map do not depend on input values. -/
theorem remap_with_prefix (n flag out : Nat) (pref : List Remap.Gate)
    (gs : List (Remap.Gate × Bool)) (mv : List Nat) (old x : List Bool)
    (nx : x.length = n) (bp : backwards pref n)
    (h : Agree mv old (evaluate pref x))
    (fr : flag < (evaluate pref x).length)
    (ok : admissible ((evaluate pref x).getD flag false) gs old)
    (ho : out < (executeOriginal gs old).length) :
    let r := rebuild flag gs (n+pref.length) mv
    let result := circuit (pref ++ r.2) (r.1.getD out 0)
    IsAO2 n result ∧ result.size + (gs.filter Prod.snd).length = pref.length + gs.length ∧
      result.eval x = (circuit (gs.map Prod.fst) out).eval old := by
  let w := evaluate pref x
  have wl : w.length = n+pref.length := by rw [show w = evaluate pref x from rfl,evaluate_length,nx]
  have rr := rebuild_correct flag gs mv old w h fr ok
  have eq := rebuild_output flag gs mv old w h fr ok out ho
  dsimp only at rr eq
  rw [wl] at rr eq
  let r := rebuild flag gs (n+pref.length) mv
  refine ⟨topology _ _ _ (backwards_append pref _ n bp rr.1),?_,?_⟩
  · change ((pref ++ r.2).map pack).length + (gs.filter Prod.snd).length = pref.length + gs.length
    simp only [List.length_map,List.length_append]
    exact rebuild_count_exact flag (n+pref.length) pref.length gs mv
  · change (circuit (pref ++ r.2) (r.1.getD out 0)).eval x = _
    unfold Circuit.eval
    rw [wires,evaluate_append,original_wires]
    exact eq


def fanoPref : List Remap.Gate := [⟨true,0,7⟩]

def fanoMap : List Nat := List.ofFn fun i : Fin 14 => if i.val = 0 then 14 else i.val

def fanoSub (x : Fin 14 → Bool) : Fin 14 → Bool :=
  fun i => if i.val = 0 then x i || x 7 else x i

private theorem getOfFn {A : Type} (f : Fin 14 → A) (i : Nat) (d : A) (hi : i < 14) :
    (List.ofFn f).getD i d = f ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  exact List.getElem_ofFn _

theorem fano_initial (x : Fin 14 → Bool) :
    Agree fanoMap (List.ofFn (fanoSub x)) (evaluate fanoPref (List.ofFn x)) := by
  refine ⟨by simp [fanoMap],?_⟩
  intro i hi
  have ilt : i < 14 := by simpa using hi
  have base : (List.ofFn x).length = 14 := by simp
  have add : evaluate fanoPref (List.ofFn x) = List.ofFn x ++ [x 0 || x 7] := by
    unfold fanoPref
    change List.ofFn x ++ [applyGate ⟨true,0,7⟩
      ((List.ofFn x).getD 0 false) ((List.ofFn x).getD 7 false)] = _
    rw [getOfFn x 0 false (by decide),getOfFn x 7 false (by decide)]
    rfl
  rw [add,show fanoMap.getD i 0 = (if i = 0 then 14 else i) from getOfFn _ i 0 ilt,
      getOfFn (fanoSub x) i false ilt]
  by_cases z : i = 0
  · subst i
    refine ⟨by simp,?_⟩
    change (List.ofFn x ++ [x 0 || x 7]).getD 14 false = fanoSub x 0
    have e := getD_end (List.ofFn x) (x 0 || x 7) false
    rw [base] at e
    exact e
  · rw [ite_eq_right z,getD_app _ _ _ _ (by simpa using ilt),getOfFn x i false ilt]
    exact ⟨by simp; omega,by simp [fanoSub,z]⟩

theorem fano_prefix_remap (gs : List (Remap.Gate × Bool)) (out : Nat)
    (x : Fin 14 → Bool)
    (valid : admissible ((evaluate fanoPref (List.ofFn x)).getD 7 false) gs
      (List.ofFn (fanoSub x)))
    (ho : out < (executeOriginal gs (List.ofFn (fanoSub x))).length) :
    let r := rebuild 7 gs 15 fanoMap
    let result := circuit (fanoPref ++ r.2) (r.1.getD out 0)
    IsAO2 14 result ∧ result.size + (gs.filter Prod.snd).length = 1 + gs.length ∧
      result.eval (List.ofFn x) = (circuit (gs.map Prod.fst) out).eval (List.ofFn (fanoSub x)) := by
  have len : (List.ofFn x).length = 14 := by simp
  have pref : backwards fanoPref 14 := by
    change 0 < 14 ∧ 7 < 14 ∧ True
    decide
  have fr : 7 < (evaluate fanoPref (List.ofFn x)).length := by
    rw [evaluate_length,len]; decide
  exact remap_with_prefix 14 7 out fanoPref gs fanoMap (List.ofFn (fanoSub x))
    (List.ofFn x) len pref (fano_initial x) fr valid ho


private theorem original_keeps (gs : List (Remap.Gate × Bool)) (old : List Bool)
    (i : Nat) (valid : i < old.length) :
    (executeOriginal gs old).getD i false = old.getD i false := by
  induction gs generalizing old with
  | nil => rfl
  | cons g gs ih =>
    have hh : i < (old ++ [value g.1 old]).length := by
      simp only [List.length_append,List.length_singleton]; omega
    change (executeOriginal gs (old ++ [value g.1 old])).getD i false = _
    rw [ih _ hh, getD_app _ _ _ _ valid]

/-- The alias premise can be stated on final old wire values, not on
an implementation-specific evaluation prefix. -/
theorem admissible_from_values (flagValue : Bool) (gs : List (Remap.Gate × Bool))
    (old : List Bool) (order : backwards (gs.map Prod.fst) old.length)
    (aliases : ∀ j (hj : j < gs.length), gs[j].2 = true →
      (executeOriginal gs old).getD (old.length+j) false = flagValue) :
    admissible flagValue gs old := by
  induction gs generalizing old with
  | nil => exact trivial
  | cons g gs ih =>
    obtain ⟨g,remove⟩ := g
    let stepOld := old ++ [value g old]
    have len : stepOld.length = old.length+1 := by simp [stepOld]
    refine ⟨order.1,order.2.1,?_,?_⟩
    · intro h
      have e := aliases 0 (by simp) h
      have keep : (executeOriginal gs stepOld).getD old.length false =
          stepOld.getD old.length false := original_keeps gs stepOld _ (by rw [len]; omega)
      change (executeOriginal gs stepOld).getD old.length false = flagValue at e
      rw [keep] at e
      exact (getD_end old (value g old) false).symm.trans e
    · apply ih stepOld
      · rw [len]
        exact order.2.2
      · intro j hj h
        have e := aliases (j+1) (by simp; omega) h
        change (executeOriginal gs stepOld).getD (old.length+(j+1)) false = flagValue at e
        have he : stepOld.length+j = old.length+(j+1) := by rw [len]; omega
        rw [he]
        exact e


def unpack (g : PEqualNP.CircuitLowerBounds.Gate) : Remap.Gate :=
  ⟨match g.op with | .or => true | _ => false,g.inputs.getD 0 0,g.inputs.getD 1 0⟩

theorem pack_unpack (g : PEqualNP.CircuitLowerBounds.Gate)
    (op : g.op = GateOp.or ∨ g.op = GateOp.and) (len : g.inputs.length = 2) :
    pack (unpack g) = g := by
  obtain ⟨o,ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,ls⟩⟩⟩ <;> simp at len
  rcases op with h | h <;> cases h <;> rfl

def tag (remove : Nat → Bool) : Nat → List PEqualNP.CircuitLowerBounds.Gate →
    List (Remap.Gate × Bool)
  | _,[] => []
  | i,g::gs => (unpack g,remove i)::tag remove (i+1) gs

@[simp] theorem tag_length (remove : Nat → Bool) (i : Nat)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    (tag remove i gs).length = gs.length := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih => simp [tag,ih]

theorem tag_first (remove : Nat → Bool) (i : Nat)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    (tag remove i gs).map Prod.fst = gs.map unpack := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih => simp [tag,ih]

theorem tag_selected (remove : Nat → Bool) (i : Nat)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : Nat) (h : j < (tag remove i gs).length) :
    (tag remove i gs)[j].2 = remove (i+j) := by
  induction gs generalizing i j with
  | nil => simp at h
  | cons g gs ih =>
    cases j with
    | zero => simp [tag]
    | succ j =>
      have h' : j < (tag remove (i+1) gs).length := by simp at h ⊢; omega
      have e := ih (i+1) j h'
      change (tag remove (i+1) gs)[j].2 = _
      rw [e]
      congr 1
      omega

theorem original_exact (n : Nat) (C : Circuit) (m : IsAO2 n C) (remove : Nat → Bool) :
    circuit ((tag remove 0 C.gates).map Prod.fst) C.output = C := by
  unfold circuit
  rw [tag_first,List.map_map]
  have h : List.map (pack ∘ unpack) C.gates = C.gates := by
    conv_rhs => rw [← List.map_id C.gates]
    apply List.map_congr_left
    intro g hg
    exact pack_unpack g ((m.1 g hg).symm) (m.2.2 g hg)
  rw [h]

private theorem find_backwards (gs : List Remap.Gate) (n : Nat)
    (bounds : ∀ j (hj : j < gs.length), gs[j].left < n+j ∧ gs[j].right < n+j) :
    backwards gs n := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    have fst := bounds 0 (by simp)
    refine ⟨fst.1,fst.2,ih (n+1) ?_⟩
    intro j hj
    have q := bounds (j+1) (by simp; omega)
    have e : n+(j+1) = n+1+j := by omega
    rw [e] at q
    exact q

theorem original_backwards (n : Nat) (C : Circuit) (m : IsAO2 n C)
    (remove : Nat → Bool) :
    backwards ((tag remove 0 C.gates).map Prod.fst) n := by
  rw [tag_first]
  apply find_backwards
  intro j hj
  have valid : j < C.gates.length := by simpa using hj
  have hs : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ valid]
    exact List.getElem_mem (l := C.gates) valid
  have fin := m.2.2 _ hs
  have back := m.2.1 j valid
  have eq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ valid
  have inps : ∃ a b, (gateAt C j).inputs = [a,b] := by
    rcases he : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,z⟩⟩⟩ <;>
      simp [he] at fin
    exact ⟨a,b,rfl⟩
  obtain ⟨a,b,e⟩ := inps
  have ba : a < n+j := back a (by simp [e])
  have bb : b < n+j := back b (by simp [e])
  simp only [List.getElem_map,←eq,unpack,e]
  exact ⟨ba,bb⟩


theorem executeOriginal_length (gs : List (Remap.Gate × Bool)) (w : List Bool) :
    (executeOriginal gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [executeOriginal]
  | cons g gs ih =>
    rcases g with ⟨a,v⟩
    rw [executeOriginal,ih]
    simp
    omega

/-- The transform applies to any ordered binary upstream circuit, not merely
a pre-encoded list. A gate selected by a fixed mask must equal line 7 under
the augmented input on every assignment. -/
theorem remap_arbitrary_fano (C : Circuit) (m : IsAO2 14 C) (remove : Nat → Bool)
    (outValid : C.output < 14 + C.gates.length)
    (aliases : ∀ x : Fin 14 → Bool, ∀ j < C.gates.length, remove j = true →
      (C.wires (List.ofFn (fanoSub x))).getD (14+j) false = x 7) :
    ∃ R : Circuit, IsAO2 14 R ∧
      R.size + ((tag remove 0 C.gates).filter Prod.snd).length = 1 + C.size ∧
      ∀ x : Fin 14 → Bool,
        R.eval (List.ofFn x) = C.eval (List.ofFn (fanoSub x)) := by
  let gs := tag remove 0 C.gates
  let r := rebuild 7 gs 15 fanoMap
  let R := circuit (fanoPref ++ r.2) (r.1.getD C.output 0)
  have h (x : Fin 14 → Bool) : IsAO2 14 R ∧
      R.size + (gs.filter Prod.snd).length = 1 + C.size ∧
      R.eval (List.ofFn x) = C.eval (List.ofFn (fanoSub x)) := by
    let old := List.ofFn (fanoSub x)
    have olen : old.length = 14 := by simp [old]
    have glen : gs.length = C.gates.length := tag_length _ _ _
    have oe : circuit (gs.map Prod.fst) C.output = C := original_exact 14 C m remove
    have ewire : (executeOriginal gs old) = C.wires old := by
      rw [← original_wires gs C.output old,oe]
    have hflag : (evaluate fanoPref (List.ofFn x)).getD 7 false = x 7 := by
      change (List.ofFn x ++ [value ⟨true,0,7⟩ (List.ofFn x)]).getD 7 false = x 7
      rw [getD_app _ _ _ _ (by simp),getOfFn x 7 false (by decide)]
      rfl
    have ad : admissible ((evaluate fanoPref (List.ofFn x)).getD 7 false) gs old := by
      rw [hflag]
      apply admissible_from_values
      · rw [olen]; exact original_backwards 14 C m remove
      · intro j hj sel
        have k := tag_selected remove 0 C.gates j hj
        have chosen : remove j = true := by
          rw [← Nat.zero_add j,k.symm]
          exact sel
        rw [ewire,olen]
        exact aliases x j (by simpa [glen] using hj) chosen
    have hoff : C.output < (executeOriginal gs old).length := by
      rwa [executeOriginal_length,olen,glen]
    have q := fano_prefix_remap gs C.output x ad hoff
    rw [oe] at q
    exact ⟨q.1,by simpa only [glen,Circuit.size] using q.2.1,q.2.2⟩
  exact ⟨R,(h (fun _ => false)).1,(h (fun _ => false)).2.1,fun x => (h x).2.2⟩

end ProofLantern.Remap.Upstream

namespace ProofLantern.ThirdPosition

def edgeWire (p l : Bool) : Bool := p && l
def starWire (p l a : Bool) : Bool := p && (l || a)

private theorem implication (p l a : Bool) :
    edgeWire p l = true → starWire p l a = true := by
  cases p <;> cases l <;> cases a <;> decide

/-- If the larger of the two adjacent prefix wires is sound, copy it into
the smaller wire. Any newly accepted row already satisfies the target. -/
theorem substituteLarger {X : Type} (target p l a : X → Bool)
    (tail : X → Bool → Bool → Bool)
    (mono : ∀ x u v, (u = true → v = true) →
      tail x (starWire (p x) (l x) (a x)) u = true →
      tail x (starWire (p x) (l x) (a x)) v = true)
    (exact : ∀ x, tail x (starWire (p x) (l x) (a x)) (edgeWire (p x) (l x)) = target x)
    (sound : ∀ x, starWire (p x) (l x) (a x) = true → target x = true) :
    ∀ x, tail x (starWire (p x) (l x) (a x)) (starWire (p x) (l x) (a x)) = target x := by
  intro x
  cases ht : target x
  · have hs : starWire (p x) (l x) (a x) = false := by
      cases hg : starWire (p x) (l x) (a x)
      · rfl
      · exact False.elim (Bool.noConfusion (ht.symm.trans (sound x hg)))
    have he : edgeWire (p x) (l x) = false := by
      cases h : edgeWire (p x) (l x)
      · rfl
      · exact False.elim (Bool.noConfusion (hs.symm.trans (implication (p x) (l x) (a x) h)))
    rw [hs]
    have check := exact x
    rwa [hs,he,ht] at check
  · exact mono x _ _ (implication (p x) (l x) (a x)) ((exact x).trans ht)

/-- If on every minimal positive witness the larger and smaller wire agree,
copy the smaller wire into the larger wire. It loses no true witness. -/
theorem substituteSmaller {X : Type} (target p l a : X → Bool)
    (tail : X → Bool → Bool → Bool) (le : X → X → Prop)
    (inWire : ∀ x u v, (u = true → v = true) →
      tail x u (edgeWire (p x) (l x)) = true → tail x v (edgeWire (p x) (l x)) = true)
    (up : ∀ x y, le y x →
      tail y (edgeWire (p y) (l y)) (edgeWire (p y) (l y)) = true →
      tail x (edgeWire (p x) (l x)) (edgeWire (p x) (l x)) = true)
    (exact : ∀ x, tail x (starWire (p x) (l x) (a x)) (edgeWire (p x) (l x)) = target x)
    (minimal : ∀ x, target x = true → ∃ y, le y x ∧ target y = true ∧
      starWire (p y) (l y) (a y) = edgeWire (p y) (l y)) :
    ∀ x, tail x (edgeWire (p x) (l x)) (edgeWire (p x) (l x)) = target x := by
  intro x
  cases hx : target x
  · cases out : tail x (edgeWire (p x) (l x)) (edgeWire (p x) (l x))
    · rfl
    · have old := inWire x _ _ (implication (p x) (l x) (a x)) out
      rw [exact x,hx] at old
      contradiction
  · obtain ⟨y,hxy,hy,ha⟩ := minimal x hx
    apply up x y hxy
    have old := (exact y).trans hy
    rw [ha] at old
    exact old


def positiveRows : List Nat :=
  (List.range 7).flatMap fun l =>
    [0,1,3].map fun d => (1 <<< (l+7)) ||| (1 <<< ((l+d)%7))

def neighboringLine (a : Nat) : Bool := a == 11 || a == 13

/- The two prefix wire formulas agree on every positive two-hot witness
when the auxiliary primary is not an incident line through point zero. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem non_neighbor_positive_agreement : ∀ a : Fin 14, a.val ≠ 0 → a.val ≠ 7 →
    neighboringLine a.val = false →
    (positiveRows.all (fun m =>
      starWire (m.testBit 0) (m.testBit 7) (m.testBit a.val) ==
      edgeWire (m.testBit 0) (m.testBit 7))) = true := by decide

theorem neighbor_rows : (positiveRows.contains ((1 <<< 0) ||| (1 <<< 7))) = true ∧
    (positiveRows.contains ((1 <<< 0) ||| (1 <<< 11))) = true ∧
    (positiveRows.contains ((1 <<< 0) ||| (1 <<< 13))) = true := by decide

end ProofLantern.ThirdPosition


namespace ProofLantern.Remap.ThirdMerge

def mergeMap (n : Nat) : List Nat := (List.range n ++ [n]) ++ [n]

theorem prefix_agreement (leading : List Bool) (shared : Bool) :
    Agree (mergeMap leading.length)
      ((leading ++ [shared]) ++ [shared]) (leading ++ [shared]) := by
  let fresh := leading ++ [shared]
  have start : Agree (List.range leading.length) leading fresh := by
    refine ⟨by simp,?_⟩
    intro i hi
    have index : (List.range leading.length).getD i 0 = i := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_range hi]
    rw [index]
    exact ⟨by simp [fresh]; omega, getD_app leading [shared] i false hi⟩
  have b : leading.length < fresh.length := by simp [fresh]
  have v : fresh.getD leading.length false = shared := getD_end leading shared false
  exact append_agree _ _ _ _ _ (append_agree _ _ _ _ _ start b v) b v

/-- Both old prefix wires become the same representative in the shortened
physical prefix. This proof handles output equal to either deleted wire. -/
theorem merge_tail (leading : List Bool) (shared : Bool) (gs : List (Remap.Gate × Bool))
    (ok : admissible shared gs ((leading ++ [shared]) ++ [shared]))
    (output : Nat)
    (outValid : output < (executeOriginal gs ((leading ++ [shared]) ++ [shared])).length) :
    let r := rebuild leading.length gs (leading ++ [shared]).length (mergeMap leading.length)
    backwards r.2 (leading ++ [shared]).length ∧
    r.2.length = (gs.filter (fun i => !i.2)).length ∧
    (evaluate r.2 (leading ++ [shared])).getD (r.1.getD output 0) false =
      (executeOriginal gs ((leading ++ [shared]) ++ [shared])).getD output false := by
  have v : (leading ++ [shared]).getD leading.length false = shared :=
    getD_end leading shared false
  have a := prefix_agreement leading shared
  have s : leading.length < (leading ++ [shared]).length := by simp
  have ok' : admissible ((leading ++ [shared]).getD leading.length false) gs
      ((leading ++ [shared]) ++ [shared]) := by rw [v]; exact ok
  exact ⟨(rebuild_correct _ _ _ _ _ a s ok').1,rebuild_count _ _ _ _,
    rebuild_output _ _ _ _ _ a s ok' output outValid⟩

end ProofLantern.Remap.ThirdMerge


namespace ProofLantern.Remap.TypedThird

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.Remap.ThirdMerge
open ProofLantern.ThirdPosition

def lead (a : Fin 14) : Remap.Gate := ⟨true,7,a.val⟩
def star : Remap.Gate := ⟨false,0,14⟩
def lastMark : Remap.Gate := ⟨false,7,15⟩
def direct : Remap.Gate := ⟨false,0,7⟩
def pref (a : Fin 14) (big : Bool) : List Remap.Gate :=
  [lead a, if big then star else direct]

def leadingValues (a : Fin 14) (x : Fin 14 → Bool) : List Bool :=
  List.ofFn x ++ [x 7 || x a]

def tailValue (suffix : List Remap.Gate) (out : Nat) (a : Fin 14) (x : Fin 14 → Bool)
    (p q : Bool) : Bool :=
  (evaluate suffix ((leadingValues a x ++ [p]) ++ [q])).getD out false

theorem leading_len (a : Fin 14) (x : Fin 14 → Bool) : (leadingValues a x).length = 15 := by
  simp [leadingValues]

private theorem leadEval (a : Fin 14) (x : Fin 14 → Bool) :
    value (lead a) (List.ofFn x) = (x 7 || x a) := by
  change ((List.ofFn x).getD 7 false || (List.ofFn x).getD a.val false) = _
  rw [getOfFn x 7 false (by decide),getOfFn x a.val false a.isLt]
  rfl

private theorem starEval (a : Fin 14) (x : Fin 14 → Bool) :
    value star (leadingValues a x) = starWire (x 0) (x 7) (x a) := by
  change ((leadingValues a x).getD 0 false && (leadingValues a x).getD 14 false) = _
  have v : (leadingValues a x).getD 14 false = (x 7 || x a) := by
    unfold leadingValues
    have e := getD_end (List.ofFn x) (x 7 || x a) false
    simpa only [List.length_ofFn] using e
  rw [v]
  unfold leadingValues
  rw [getD_app _ _ _ _ (by simp),getOfFn x 0 false (by decide)]
  rfl

private theorem edgeEval (a : Fin 14) (x : Fin 14 → Bool) :
    value direct (leadingValues a x) = edgeWire (x 0) (x 7) := by
  change ((leadingValues a x).getD 0 false && (leadingValues a x).getD 7 false) = _
  unfold leadingValues
  rw [getD_app _ _ 0 _ (by simp),getD_app _ _ 7 _ (by simp),
    getOfFn x 0 false (by decide),getOfFn x 7 false (by decide)]
  rfl

private theorem nestedEval (a : Fin 14) (x : Fin 14 → Bool) :
    value lastMark (leadingValues a x ++ [starWire (x 0) (x 7) (x a)]) =
      edgeWire (x 0) (x 7) := by
  change (((leadingValues a x ++ [_]).getD 7 false) &&
       ((leadingValues a x ++ [_]).getD 15 false)) = _
  have len := leading_len a x
  have v : (leadingValues a x ++ [starWire (x 0) (x 7) (x a)]).getD 15 false =
      starWire (x 0) (x 7) (x a) := by
    have e := getD_end (leadingValues a x) (starWire (x 0) (x 7) (x a)) false
    rwa [len] at e
  rw [v,getD_app _ _ 7 _ (by rw [len]; decide)]
  unfold leadingValues
  rw [getD_app _ _ 7 _ (by simp),getOfFn x 7 false (by decide)]
  let q := x a
  change (x 7 && starWire (x 0) (x 7) q) = edgeWire (x 0) (x 7)
  cases x 0 <;> cases x 7 <;> cases q <;> rfl

theorem canonical_eval (a : Fin 14) (suffix : List Remap.Gate) (out : Nat) (x : Fin 14 → Bool) :
    (circuit ([lead a,star,lastMark] ++ suffix) out).eval (List.ofFn x) =
      tailValue suffix out a x (starWire (x 0) (x 7) (x a)) (edgeWire (x 0) (x 7)) := by
  unfold Circuit.eval
  rw [wires]
  change (evaluate (star::lastMark::suffix)
    (List.ofFn x ++ [value (lead a) (List.ofFn x)])).getD out false = _
  rw [leadEval]
  change (evaluate (lastMark::suffix) (leadingValues a x ++ [value star (leadingValues a x)])).getD out false = _
  rw [starEval]
  change (evaluate suffix ((leadingValues a x ++ [starWire (x 0) (x 7) (x a)]) ++
      [value lastMark (leadingValues a x ++ [starWire (x 0) (x 7) (x a)])])).getD out false = _
  rw [nestedEval]
  rfl

def shared (a : Fin 14) (big : Bool) (x : Fin 14 → Bool) : Bool :=
  if big then starWire (x 0) (x 7) (x a) else edgeWire (x 0) (x 7)

private theorem pref_eval (a : Fin 14) (big : Bool) (x : Fin 14 → Bool) :
    evaluate (pref a big) (List.ofFn x) = leadingValues a x ++ [shared a big x] := by
  cases big
  · change (List.ofFn x ++ [value (lead a) (List.ofFn x)]) ++ [_] = _
    rw [leadEval]
    change leadingValues a x ++ [value direct (leadingValues a x)] = _
    rw [edgeEval]
    rfl
  · change (List.ofFn x ++ [value (lead a) (List.ofFn x)]) ++ [_] = _
    rw [leadEval]
    change leadingValues a x ++ [value star (leadingValues a x)] = _
    rw [starEval]
    rfl

def tagKeep (gs : List Remap.Gate) := gs.map fun g => (g,false)

private theorem fst_keep (gs : List Remap.Gate) : (tagKeep gs).map Prod.fst = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [tagKeep] at ih ⊢; exact ih

private theorem eval_keep (gs : List Remap.Gate) (w : List Bool) :
    executeOriginal (tagKeep gs) w = evaluate gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem length_keep (gs : List Remap.Gate) :
    ((tagKeep gs).filter (fun g => !g.2)).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [tagKeep] using congrArg Nat.succ ih

private theorem all_keep (gs : List Remap.Gate) (w : List Bool) (v : Bool)
    (h : backwards gs w.length) : admissible v (tagKeep gs) w := by
  apply admissible_from_values
  · rw [fst_keep]; exact h
  · intro j hj ht
    simp [tagKeep] at ht

def rebuildTail (suffix : List Remap.Gate) :=
  rebuild 15 (tagKeep suffix) 16 (mergeMap 15)

def contracted (a : Fin 14) (big : Bool) (suffix : List Remap.Gate) (out : Nat) : Circuit :=
  let r := rebuildTail suffix
  circuit (pref a big ++ r.2) (r.1.getD out 0)

/-- The physical two-gate prefix plus remapped suffix evaluates exactly
like the old suffix with both old gate wires fed by the single shared wire. -/
theorem physical_prefix_merge (a : Fin 14) (big : Bool) (suffix : List Remap.Gate)
    (tailBack : backwards suffix 17) (out : Nat) (oo : out < 17+suffix.length)
    (x : Fin 14 → Bool) :
    IsAO2 14 (contracted a big suffix out) ∧
    (contracted a big suffix out).size = 2+suffix.length ∧
    (contracted a big suffix out).eval (List.ofFn x) =
       tailValue suffix out a x (shared a big x) (shared a big x) := by
  let lim := leadingValues a x
  let sh := shared a big x
  let w := (lim ++ [sh]) ++ [sh]
  have len : lim.length = 15 := leading_len a x
  have ow : w.length = 17 := by simp [w,len]
  have ad := all_keep suffix w sh (by rw [ow]; exact tailBack)
  have ov : out < (executeOriginal (tagKeep suffix) w).length := by
    rw [executeOriginal_length,ow]
    simpa [tagKeep] using oo
  have r := merge_tail lim sh (tagKeep suffix) ad out ov
  dsimp only at r
  have lin : (lim ++ [sh]).length = 16 := by simp [len]
  rw [lin,len,eval_keep,length_keep] at r
  have pb : backwards (pref a big) 14 := by
    have ha := a.isLt
    cases big
    · exact ⟨by change 7 < 14; decide,ha,by decide,by decide,trivial⟩
    · exact ⟨by change 7 < 14; decide,ha,by decide,by decide,trivial⟩
  have bt : backwards (rebuildTail suffix).2 (14+(pref a big).length) := by
    have e : (pref a big).length = 2 := rfl
    rw [e]
    exact r.1
  refine ⟨topology _ _ _ (backwards_append _ _ _ pb bt),?_,?_⟩
  · unfold contracted Circuit.size circuit
    simp only [List.length_map,List.length_append,rebuildTail,(show (pref a big).length=2 by rfl)]
    rw [r.2.1]
  · unfold contracted Circuit.eval
    rw [wires,evaluate_append,pref_eval]
    exact r.2.2

end ProofLantern.Remap.TypedThird

namespace ProofLantern.Remap.TypedThird

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.ThirdPosition

def ListBelow (a b : List Bool) : Prop :=
  a.length=b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

private theorem bool_or_le {a b c d : Bool} (ac : a = true → c = true)
    (bd : b = true → d = true) : (a || b) = true → (c || d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem bool_and_le {a b c d : Bool} (ac : a = true → c = true)
    (bd : b = true → d = true) : (a && b) = true → (c && d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem value_below (g : Remap.Gate) (a b : List Bool) (h : ListBelow a b) :
    value g a = true → value g b = true := by
  unfold value applyGate
  split
  · exact bool_or_le (h.2 g.left) (h.2 g.right)
  · exact bool_and_le (h.2 g.left) (h.2 g.right)

private theorem same_below (w : List Bool) : ListBelow w w := ⟨rfl,fun _ h => h⟩

theorem append_below (a b : List Bool) (p q : Bool) (h : ListBelow a b)
    (pq : p = true → q = true) : ListBelow (a++[p]) (b++[q]) := by
  refine ⟨by simp [h.1],?_⟩
  intro i hi
  rcases Nat.lt_trichotomy i a.length with ha | ha | ha
  · rw [getD_app _ _ _ _ ha] at hi
    rw [getD_app _ _ _ _ (by rw [←h.1]; exact ha)]
    exact h.2 _ hi
  · subst i
    rw [getD_end] at hi
    rw [h.1,getD_end]
    exact pq hi
  · have zero : (a++[p]).getD i false = false := List.getD_eq_default _ _ (by
      simp only [List.length_append,List.length_singleton]; omega)
    rw [zero] at hi
    contradiction

theorem eval_below (gs : List Remap.Gate) (a b : List Bool) (h : ListBelow a b) :
    ListBelow (evaluate gs a) (evaluate gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih => exact ih _ _ (append_below _ _ _ _ h (value_below g a b h))

def VertBelow (x y : Fin 14 → Bool) : Prop :=
  ∀ i, x i = true → y i = true

private theorem ofFn_below {x y : Fin 14 → Bool} (h : VertBelow x y) :
    ListBelow (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp,?_⟩
  intro i hi
  by_cases hv : i < 14
  · rw [getOfFn _ i false hv] at hi ⊢
    exact h _ hi
  · have e : (List.ofFn x).getD i false = false := List.getD_eq_default _ _
      (by simp; omega)
    rw [e] at hi
    contradiction

private theorem leading_below (a : Fin 14) {x y : Fin 14 → Bool} (h : VertBelow x y) :
    ListBelow (leadingValues a x) (leadingValues a y) :=
  append_below _ _ _ _ (ofFn_below h) (bool_or_le (h 7) (h a))

private theorem ascending_edge_copy (a : Fin 14) (suf : List Remap.Gate) (out : Nat)
    (x y : Fin 14 → Bool) (h : VertBelow x y) :
    tailValue suf out a x (edgeWire (x 0) (x 7)) (edgeWire (x 0) (x 7)) = true →
    tailValue suf out a y (edgeWire (y 0) (y 7)) (edgeWire (y 0) (y 7)) = true := by
  have edgeLe : edgeWire (x 0) (x 7) = true → edgeWire (y 0) (y 7) = true :=
    bool_and_le (h 0) (h 7)
  exact (eval_below suf _ _ (append_below _ _ _ _
    (append_below _ _ _ _ (leading_below a h) edgeLe) edgeLe)).2 out

theorem canonical_rewrite_larger (a : Fin 14) (suf : List Remap.Gate) (out : Nat)
    (ord : backwards suf 17) (ot : out < 17+suf.length)
    (F : (Fin 14 → Bool) → Bool)
    (oldExact : ∀ x, (circuit ([lead a,star,lastMark]++suf) out).eval (List.ofFn x) = F x)
    (sound : ∀ x, starWire (x 0) (x 7) (x a) = true → F x = true) :
    ∃ R : Circuit, IsAO2 14 R ∧ R.size+1=(circuit ([lead a,star,lastMark]++suf) out).size ∧
       ∀ x, R.eval (List.ofFn x) = F x := by
  have step (x : Fin 14 → Bool) (p q : Bool) (pq : p = true → q = true) :
      tailValue suf out a x (starWire (x 0) (x 7) (x a)) p = true →
      tailValue suf out a x (starWire (x 0) (x 7) (x a)) q = true :=
    (eval_below suf _ _ (append_below _ _ _ _ (same_below _) pq)).2 out
  have old (x : Fin 14 → Bool) :
      tailValue suf out a x (starWire (x 0) (x 7) (x a)) (edgeWire (x 0) (x 7)) = F x :=
    (canonical_eval a suf out x).symm.trans (oldExact x)
  have eq := substituteLarger F (fun x => x 0) (fun x => x 7) (fun x => x a)
    (tailValue suf out a) step old sound
  have shape := physical_prefix_merge a true suf ord out ot (fun _ => false)
  refine ⟨contracted a true suf out,shape.1,?_,?_⟩
  · rw [shape.2.1]
    simp [Circuit.size,circuit]
    omega
  · intro x
    rw [(physical_prefix_merge a true suf ord out ot x).2.2]
    exact eq x

theorem canonical_rewrite_smaller (a : Fin 14) (suf : List Remap.Gate) (out : Nat)
    (ord : backwards suf 17) (ot : out < 17+suf.length)
    (F : (Fin 14 → Bool) → Bool)
    (oldExact : ∀ x, (circuit ([lead a,star,lastMark]++suf) out).eval (List.ofFn x) = F x)
    (minima : ∀ x, F x = true → ∃ y, VertBelow y x ∧ F y = true ∧
       starWire (y 0) (y 7) (y a) = edgeWire (y 0) (y 7)) :
    ∃ R : Circuit, IsAO2 14 R ∧ R.size+1=(circuit ([lead a,star,lastMark]++suf) out).size ∧
       ∀ x, R.eval (List.ofFn x) = F x := by
  have step (x : Fin 14 → Bool) (p q : Bool) (pq : p = true → q = true) :
      tailValue suf out a x p (edgeWire (x 0) (x 7)) = true →
      tailValue suf out a x q (edgeWire (x 0) (x 7)) = true :=
    (eval_below suf _ _ (append_below _ _ _ _
      (append_below _ _ _ _ (same_below _) pq) (fun h => h))).2 out
  have old (x : Fin 14 → Bool) :
      tailValue suf out a x (starWire (x 0) (x 7) (x a)) (edgeWire (x 0) (x 7)) = F x :=
    (canonical_eval a suf out x).symm.trans (oldExact x)
  have eq := substituteSmaller F (fun x => x 0) (fun x => x 7) (fun x => x a)
    (tailValue suf out a) VertBelow step (fun x y => ascending_edge_copy a suf out y x) old minima
  have shape := physical_prefix_merge a false suf ord out ot (fun _ => false)
  refine ⟨contracted a false suf out,shape.1,?_,?_⟩
  · rw [shape.2.1]
    simp [Circuit.size,circuit]
    omega
  · intro x
    rw [(physical_prefix_merge a false suf ord out ot x).2.2]
    exact eq x

end ProofLantern.Remap.TypedThird

namespace ProofLantern.Remap.TypedThird

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.ThirdPosition

def incidence (p l : Fin 7) : Prop := p = l ∨ p = l+1 ∨ p = l+3
def fano (x : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 7, incidence p l ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

def fanoBool (x : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

theorem fanoBool_true (x : Fin 14 → Bool) : fanoBool x = true ↔ fano x := by
  simp [fanoBool,fano,incidence]

def seed (p l : Fin 7) (i : Fin 14) : Bool :=
  decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4096 in
private theorem exact_seed_eq : ∀ (a : Fin 14) (p l : Fin 7),
    a.val ≠ 0 → a.val ≠ 7 → neighboringLine a.val = false →
    (p = l ∨ p = l+1 ∨ p = l+3) →
    starWire (seed p l 0) (seed p l 7) (seed p l a) =
      edgeWire (seed p l 0) (seed p l 7) := by decide

private theorem checked_minima (a : Fin 14) (a0 : a.val ≠ 0) (a7 : a.val ≠ 7)
    (non : neighboringLine a.val = false) (x : Fin 14 → Bool) (hit : fanoBool x = true) :
    ∃ y, VertBelow y x ∧ fanoBool y = true ∧
      starWire (y 0) (y 7) (y a) = edgeWire (y 0) (y 7) := by
  obtain ⟨p,l,inc,px,lx⟩ := (fanoBool_true _).mp hit
  refine ⟨seed p l,?_,(fanoBool_true _).mpr ⟨p,l,inc,by simp [seed],by simp [seed]⟩,
    exact_seed_eq a p l a0 a7 non inc⟩
  intro i h
  have eq : i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := decide_eq_true_eq.mp h
  rcases eq with e | e <;> subst i <;> assumption

private theorem checked_sound (a : Fin 14) (adj : neighboringLine a.val = true)
    (x : Fin 14 → Bool) (pos : starWire (x 0) (x 7) (x a) = true) :
    fanoBool x = true := by
  unfold starWire at pos
  rw [Bool.and_eq_true, Bool.or_eq_true] at pos
  apply (fanoBool_true _).mpr
  obtain ⟨p, l | h⟩ := pos
  · exact ⟨0,0,Or.inl rfl,p,l⟩
  · have opts : a.val = 11 ∨ a.val = 13 := by simpa [neighboringLine] using adj
    rcases opts with h11 | h13
    · have ea : a = (11 : Fin 14) := Fin.ext h11
      rw [ea] at h
      exact ⟨0,4,Or.inr (Or.inr rfl),p,h⟩
    · have ea : a = (13 : Fin 14) := Fin.ext h13
      rw [ea] at h
      exact ⟨0,6,Or.inr (Or.inl rfl),p,h⟩

/-- The remaining canonical third-gate templates cannot be minimum,
whatever valid monotone suffix follows them. -/
theorem canonical_third_not_minimum
    (floor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) → 27 ≤ C.size)
    (a : Fin 14) (a0 : a.val ≠ 0) (a7 : a.val ≠ 7)
    (suffix : List Remap.Gate) (out : Nat)
    (tailOrder : backwards suffix 17) (validOut : out < 17+suffix.length)
    (budget : (circuit ([lead a,star,lastMark]++suffix) out).size ≤ 27)
    (target : ∀ x : Fin 14 → Bool,
      (circuit ([lead a,star,lastMark]++suffix) out).eval (List.ofFn x) = true ↔ fano x) :
    False := by
  have meaning (x : Fin 14 → Bool) :
      (circuit ([lead a,star,lastMark]++suffix) out).eval (List.ofFn x) = fanoBool x := by
    have q := (target x).trans (fanoBool_true x).symm
    cases h : (circuit ([lead a,star,lastMark]++suffix) out).eval (List.ofFn x)
    · cases hb : fanoBool x
      · rfl
      · have bad := q.mpr hb
        rw [h] at bad
        contradiction
    · exact (q.mp h).symm
  have result : ∃ R : Circuit, IsAO2 14 R ∧
      R.size+1 = (circuit ([lead a,star,lastMark]++suffix) out).size ∧
      ∀ x, R.eval (List.ofFn x) = fanoBool x := by
    cases adj : neighboringLine a.val
    · exact canonical_rewrite_smaller a suffix out tailOrder validOut fanoBool meaning
        (checked_minima a a0 a7 adj)
    · exact canonical_rewrite_larger a suffix out tailOrder validOut fanoBool meaning
        (checked_sound a adj)
  obtain ⟨R,hm,hs,hr⟩ := result
  have n := floor R hm (fun x => (by rw [hr]; exact fanoBool_true x))
  omega

end ProofLantern.Remap.TypedThird


namespace ProofLantern.Remap.TypedThird

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream

def redirectMap (n target : Nat) : List Nat := List.range n ++ [target]

def redirected (n target : Nat) (pre suf : List Remap.Gate) (out : Nat) : Circuit :=
  let r := rebuild target (tagKeep suf) (n+pre.length) (redirectMap (n+pre.length) target)
  circuit (pre ++ r.2) (r.1.getD out 0)

private theorem range_agrees (w : List Bool) : Agree (List.range w.length) w w := by
  refine ⟨by simp,?_⟩
  intro i hi
  have h : (List.range w.length).getD i 0 = i := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_range hi]
  rw [h]
  exact ⟨hi,rfl⟩

/-- Remove a designated gate, redirecting every outgoing use (including
the output) to a preceding wire. The shortened circuit matches the
original tail fed the changed prefix value, for every assignment. -/
theorem redirect_earlier_physical (n target : Nat) (pre suf : List Remap.Gate)
    (hpre : backwards pre n) (hsuf : backwards suf (n+pre.length+1))
    (live : target < n+pre.length) (out : Nat)
    (valid : out < n+pre.length+1+suf.length)
    (x : List Bool) (len : x.length = n) :
    let w := evaluate pre x
    IsAO2 n (redirected n target pre suf out) ∧
      (redirected n target pre suf out).size = pre.length+suf.length ∧
      (redirected n target pre suf out).eval x =
        (evaluate suf (w ++ [w.getD target false])).getD out false := by
  let w := evaluate pre x
  have wl : w.length = n+pre.length := by
    dsimp only [w]
    rw [evaluate_length,len]
  have earlier : target < w.length := by rwa [wl]
  let old := w ++ [w.getD target false]
  have oldLen : old.length = n+pre.length+1 := by simp [old,wl]
  have ar : Agree (redirectMap (n+pre.length) target) old w := by
    rw [←wl]
    exact append_agree _ _ _ _ _ (range_agrees w) earlier rfl
  have elig : admissible (w.getD target false) (tagKeep suf) old :=
    all_keep _ _ _ (by rwa [oldLen])
  have ho : out < (executeOriginal (tagKeep suf) old).length := by
    rw [executeOriginal_length,oldLen]
    simpa [tagKeep] using valid
  have a := rebuild_correct target (tagKeep suf) (redirectMap (n+pre.length) target)
    old w ar earlier elig
  have ev := rebuild_output target (tagKeep suf) (redirectMap (n+pre.length) target)
    old w ar earlier elig out ho
  dsimp only at a
  dsimp only at ev
  rw [wl] at a ev
  let R := redirected n target pre suf out
  change IsAO2 n R ∧ R.size = _ ∧ R.eval x = _
  refine ⟨topology _ _ _ (backwards_append _ _ _ hpre a.1),?_,?_⟩
  · have sl := rebuild_count target (n+pre.length) (tagKeep suf) (redirectMap (n+pre.length) target)
    rw [length_keep] at sl
    unfold R redirected circuit Circuit.size
    simp only [List.length_map,List.length_append]
    rw [sl]
  · unfold R redirected Circuit.eval
    rw [wires,evaluate_append]
    rw [eval_keep] at ev
    exact ev

end ProofLantern.Remap.TypedThird

namespace ProofLantern.ThirdShape

inductive Prior where
  | raw (i : Nat)
  | first
  deriving DecidableEq

def src (p q : Nat) (x : Nat → Bool) : Prior → Bool
  | .raw i => x i
  | .first => x p || x q

def zeroBase (p q : Nat) := src p q (fun i => decide (i=0))
def lineBase (p q : Nat) := src p q (fun i => decide (i=7))

def combine (isOr a b : Bool) : Bool := if isOr then a || b else a && b

def secondValue (p q : Nat) (isOr : Bool) (a b : Prior) (x : Nat → Bool) :=
  combine isOr (src p q x a) (src p q x b)

def secondDelta (p q : Nat) (isOr : Bool) (a b : Prior) : Bool :=
  if isOr then lineBase p q a || lineBase p q b
  else (zeroBase p q a && lineBase p q b) || (lineBase p q a && zeroBase p q b)

def Pair {A : Type} (p q a b : A) : Prop :=
  (p=a ∧ q=b) ∨ (p=b ∧ q=a)

def Canonical (p q : Nat) (a b : Prior) :=
  ∃ u : Nat, u ≠ 0 ∧ u ≠ 7 ∧ Pair p q 7 u ∧ Pair a b (.raw 0) .first

private theorem first_info (p q : Nat) (neq : p≠q)
    (z : zeroBase p q .first = false) (l : lineBase p q .first = true) :
    ∃ u : Nat, u≠0 ∧ u≠7 ∧ Pair p q 7 u := by
  have pp : p ≠ 0 := by
    intro h; subst p; simp [zeroBase,src] at z
  have qq : q ≠ 0 := by
    intro h; subst q; simp [zeroBase,src] at z
  have hh : p=7 ∨ q=7 := by simpa [lineBase,src] using l
  rcases hh with he | he
  · exact ⟨q,qq,fun h => neq (he.trans h.symm),Or.inl ⟨he,rfl⟩⟩
  · exact ⟨p,pp,fun h => neq (h.trans he.symm),Or.inr ⟨rfl,he⟩⟩

private theorem active (p q : Nat) (ne : p≠q) (a b : Prior)
    (distinct : a≠b) (az : zeroBase p q a = true)
    (bl : lineBase p q b = true)
    (zero : (zeroBase p q a && zeroBase p q b) = false) :
    b = .raw 7 ∨ Canonical p q a b := by
  cases b with
  | raw i =>
    have h : i=7 := by simpa [lineBase,src] using bl
    exact Or.inl (congrArg Prior.raw h)
  | first =>
    cases a with
    | first => exact False.elim (distinct rfl)
    | raw i =>
      have h : i=0 := by simpa [zeroBase,src] using az
      have zz : zeroBase p q .first = false := by
        rw [az] at zero
        exact zero
      obtain ⟨u,h0,h7,pq⟩ := first_info p q ne zz bl
      exact Or.inr ⟨u,h0,h7,pq,Or.inl ⟨congrArg Prior.raw h,rfl⟩⟩

private theorem canonical_symm {p q : Nat} {a b : Prior} (h : Canonical p q b a) :
    Canonical p q a b := by
  obtain ⟨u,h0,h7,pq,ba⟩ := h
  refine ⟨u,h0,h7,pq,?_⟩
  rcases ba with ⟨q,w⟩ | ⟨q,w⟩
  · exact Or.inr ⟨w,q⟩
  · exact Or.inl ⟨w,q⟩

/-- Only the second prefix wire can carry the nonbare operand in this
case. An AND with true point-to-line trace but rejecting both singleton
bases either contains bare line as input (so the mark copies it), or has
the 12 canonical templates with one other raw primary. -/
theorem classification (p q : Nat) (ne : p≠q) (isOr : Bool) (a b : Prior)
    (distinct : a≠b)
    (zero : secondValue p q isOr a b (fun i => decide (i=0)) = false)
    (line : secondValue p q isOr a b (fun i => decide (i=7)) = false)
    (tr : secondDelta p q isOr a b = true) :
    isOr = false ∧ (a = .raw 7 ∨ b = .raw 7 ∨ Canonical p q a b) := by
  cases isOr
  · refine ⟨rfl,?_⟩
    change (zeroBase p q a && zeroBase p q b) = false at zero
    unfold secondDelta at tr
    simp only [Bool.false_eq_true, ite_false,Bool.or_eq_true,Bool.and_eq_true] at tr
    rcases tr with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rcases active p q ne a b distinct ha hb zero with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have swap : (zeroBase p q b && zeroBase p q a) = false := by
        rw [Bool.and_comm]; exact zero
      rcases active p q ne b a distinct.symm hb ha swap with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (canonical_symm h))
  · change (lineBase p q a || lineBase p q b) = false at line
    change (lineBase p q a || lineBase p q b) = true at tr
    rw [line] at tr
    contradiction

theorem duplicate_second (p q : Nat) (a b : Prior)
    (direct : a = .raw 7 ∨ b = .raw 7) (x : Nat → Bool) :
    (x 7 && secondValue p q false a b x) = secondValue p q false a b x := by
  rcases direct with h | h
  · subst a
    change (x 7 && (x 7 && src p q x b)) = (x 7 && src p q x b)
    cases x 7 <;> rfl
  · subst b
    change (x 7 && (src p q x a && x 7)) = (src p q x a && x 7)
    cases x 7 <;> cases src p q x a <;> rfl

end ProofLantern.ThirdShape

namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.Remap.TypedThird
open ProofLantern.ThirdShape ProofLantern.ThirdPosition

def index : Prior → Nat
  | .raw i => i
  | .first => 14

def validPrior : Prior → Prop
  | .raw i => i<14
  | .first => True

def firstGate (p q : Fin 14) : Remap.Gate := ⟨true,p.val,q.val⟩
def secondGate (isOr : Bool) (a b : Prior) : Remap.Gate := ⟨isOr,index a,index b⟩

def fn (x : Fin 14 → Bool) (i : Nat) : Bool := (List.ofFn x).getD i false

private theorem fnGet (x : Fin 14 → Bool) (i : Fin 14) : fn x i.val = x i :=
  getOfFn x i.val false i.isLt

def beforeTwo (p q : Fin 14) (x : Fin 14 → Bool) : List Bool :=
  List.ofFn x ++ [x p || x q]

private theorem first_values (p q : Fin 14) (x : Fin 14 → Bool) :
    evaluate [firstGate p q] (List.ofFn x) = beforeTwo p q x := by
  change List.ofFn x ++ [fn x p.val || fn x q.val] = _
  rw [fnGet x p,fnGet x q]
  rfl

private theorem read_prior (p q : Fin 14) (x : Fin 14 → Bool) (a : Prior)
    (h : validPrior a) :
    (beforeTwo p q x).getD (index a) false = src p.val q.val (fn x) a := by
  cases a with
  | raw i =>
    change (List.ofFn x ++ [_]).getD i false = (List.ofFn x).getD i false
    exact getD_app _ _ _ _ (by change i < 14 at h; simpa using h)
  | first =>
    unfold index src beforeTwo
    rw [fnGet x p,fnGet x q]
    have e := getD_end (List.ofFn x) (x p || x q) false
    simpa only [List.length_ofFn] using e

private theorem second_values (p q : Fin 14) (o : Bool) (a b : Prior)
    (ha : validPrior a) (hb : validPrior b) (x : Fin 14 → Bool) :
    evaluate [firstGate p q,secondGate o a b] (List.ofFn x) =
      beforeTwo p q x ++ [secondValue p.val q.val o a b (fn x)] := by
  rw [show [firstGate p q,secondGate o a b] = [firstGate p q]++[secondGate o a b] from rfl]
  rw [evaluate_append,first_values]
  change beforeTwo p q x ++ [combine o ((beforeTwo p q x).getD (index a) false)
    ((beforeTwo p q x).getD (index b) false)] = _
  rw [read_prior p q x a ha,read_prior p q x b hb]
  rfl

private theorem earlier_order (p q : Fin 14) (o : Bool) (a b : Prior)
    (ha : validPrior a) (hb : validPrior b) :
    backwards [firstGate p q,secondGate o a b] 14 := by
  have safe (r : Prior) (hr : validPrior r) : index r < 15 := by
    cases r with
    | first => decide
    | raw i => change i<15; change i<14 at hr; omega
  exact ⟨p.isLt,q.isLt,safe a ha,safe b hb,trivial⟩

private theorem last_value (p q : Fin 14) (o : Bool) (a b : Prior)
    (ha : validPrior a) (hb : validPrior b) (x : Fin 14 → Bool) :
    let w := evaluate [firstGate p q,secondGate o a b] (List.ofFn x)
    value lastMark w = (x 7 && secondValue p.val q.val o a b (fn x)) := by
  rw [second_values p q o a b ha hb x]
  let v := secondValue p.val q.val o a b (fn x)
  change ((beforeTwo p q x ++ [v]).getD 7 false &&
      (beforeTwo p q x ++ [v]).getD 15 false) = (x 7 && v)
  have l : (beforeTwo p q x).length = 15 := by simp [beforeTwo]
  have d : (beforeTwo p q x ++ [v]).getD 15 false = v := by
    have e := getD_end (beforeTwo p q x) v false
    rwa [l] at e
  rw [d,getD_app _ _ 7 _ (by rw [l]; decide)]
  unfold beforeTwo
  rw [getD_app _ _ 7 _ (by simp),getOfFn x 7 false (by decide)]
  rfl

private theorem canonical_assignment (p q : Fin 14) (a b : Prior)
    (ha : validPrior a) (hb : validPrior b) (aux : Fin 14)
    (pq : Pair p.val q.val 7 aux.val) (ab : Pair a b (.raw 0) .first)
    (x : Fin 14 → Bool) :
    evaluate [firstGate p q,secondGate false a b,lastMark] (List.ofFn x) =
      evaluate [lead aux,star,lastMark] (List.ofFn x) := by
  have e0 : beforeTwo p q x = leadingValues aux x := by
    unfold beforeTwo leadingValues
    rcases pq with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hp : p = (7 : Fin 14) := Fin.ext h1
      have hq : q = aux := Fin.ext h2
      rw [hp,hq]
    · have hp : p = aux := Fin.ext h1
      have hq : q = (7 : Fin 14) := Fin.ext h2
      rw [hp,hq,Bool.or_comm (x aux) (x 7)]
  have e1 : secondValue p.val q.val false a b (fn x) = starWire (x 0) (x 7) (x aux) := by
    have px : fn x p.val = x p := fnGet x p
    have qx : fn x q.val = x q := fnGet x q
    have zx : fn x 0 = x 0 := fnGet x 0
    have orval : (x p || x q) = (x 7 || x aux) := by
      rcases pq with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have hp : p = (7 : Fin 14) := Fin.ext h1
        have hq : q = aux := Fin.ext h2
        rw [hp,hq]
      · have hp : p = aux := Fin.ext h1
        have hq : q = (7 : Fin 14) := Fin.ext h2
        rw [hp,hq,Bool.or_comm]
    rcases ab with ⟨ah,bh⟩ | ⟨ah,bh⟩
    · rw [ah,bh]
      change (fn x 0 && (fn x p.val || fn x q.val)) = _
      rw [zx,px,qx,orval]; rfl
    · rw [ah,bh]
      change ((fn x p.val || fn x q.val) && fn x 0) = _
      rw [zx,px,qx,orval,Bool.and_comm]; rfl
  rw [show [firstGate p q,secondGate false a b,lastMark] =
      [firstGate p q,secondGate false a b]++[lastMark] from rfl,
    show [lead aux,star,lastMark] = pref aux true ++ [lastMark] from rfl,
    evaluate_append,evaluate_append,second_values p q false a b ha hb x,e0,e1,pref_eval]
  rfl

theorem excludes_nonbare_second_wire
    (floor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) → 27 ≤ C.size)
    (p q : Fin 14) (ne : p.val≠q.val) (o : Bool) (a b : Prior)
    (ha : validPrior a) (hb : validPrior b) (sep : a≠b)
    (zero : secondValue p.val q.val o a b (fun i => decide (i=0)) = false)
    (line : secondValue p.val q.val o a b (fun i => decide (i=7)) = false)
    (d : secondDelta p.val q.val o a b = true)
    (suf : List Remap.Gate) (ord : backwards suf 17) (out : Nat)
    (validOut : out < 17+suf.length)
    (max : (circuit ([firstGate p q,secondGate o a b,lastMark]++suf) out).size ≤ 27)
    (spec : ∀ x : Fin 14 → Bool,
      (circuit ([firstGate p q,secondGate o a b,lastMark]++suf) out).eval (List.ofFn x)=true ↔ fano x) :
    False := by
  obtain ⟨oo,h⟩ := classification p.val q.val ne o a b sep zero line d
  subst o
  have dup (use : a = .raw 7 ∨ b = .raw 7) : False := by
    let pre := [firstGate p q,secondGate false a b]
    let R := redirected 14 15 pre suf out
    have wOrd : backwards pre 14 := earlier_order p q false a b ha hb
    have pt (x : Fin 14 → Bool) := redirect_earlier_physical 14 15 pre suf wOrd ord
      (by change 15 < 16; decide) out validOut (List.ofFn x) (by simp)
    have eq (x : Fin 14 → Bool) :
        R.eval (List.ofFn x) = (circuit (pre++lastMark::suf) out).eval (List.ofFn x) := by
      change (redirected 14 15 pre suf out).eval (List.ofFn x) = _
      rw [(pt x).2.2,Circuit.eval,wires,evaluate_append]
      change (evaluate suf (_ ++ [(evaluate pre (List.ofFn x)).getD 15 false])).getD out false =
        (evaluate suf (_ ++ [value lastMark (evaluate pre (List.ofFn x))])).getD out false
      have ed := last_value p q false a b ha hb x
      dsimp only at ed
      rw [show x 7 = fn x 7 from (fnGet x 7).symm,duplicate_second p.val q.val a b use (fn x)] at ed
      rw [ed]
      rw [second_values p q false a b ha hb x]
      have ef := getD_end (beforeTwo p q x) (secondValue p.val q.val false a b (fn x)) false
      have ll : (beforeTwo p q x).length = 15 := by simp [beforeTwo]
      rw [ll] at ef
      rw [ef]
    have lb := floor R (pt (fun _ => false)).1 (by intro x; rw [eq]; exact spec x)
    have rs := (pt (fun _ => false)).2.1
    have orig : (circuit (pre++lastMark::suf) out).size = 3+suf.length := by
      simp [pre,Circuit.size,circuit]; omega
    change R.size = 2+suf.length at rs
    change (circuit (pre++lastMark::suf) out).size ≤ 27 at max
    omega
  rcases h with ha | hb | ⟨aux,h0,h7,hpq,hab⟩
  · exact dup (Or.inl ha)
  · exact dup (Or.inr hb)
  · have less : aux < 14 := by rcases hpq with ⟨_,h⟩ | ⟨h,_⟩ <;> omega
    let t : Fin 14 := ⟨aux,less⟩
    apply canonical_third_not_minimum floor t h0 h7 suf out ord validOut
    · simpa [Circuit.size,circuit] using max
    · intro x
      have e := canonical_assignment p q a b ha hb t hpq hab x
      have eq : (circuit ([firstGate p q,secondGate false a b,lastMark]++suf) out).eval (List.ofFn x) =
          (circuit ([lead t,star,lastMark]++suf) out).eval (List.ofFn x) := by
        unfold Circuit.eval
        rw [wires,wires,evaluate_append,evaluate_append,e]
        rfl
      rw [←eq]
      exact spec x

end ProofLantern.Remap.ThirdClosed

namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.Remap.TypedThird ProofLantern.ThirdShape

def firstMark : Remap.Gate := ⟨false,7,14⟩

/-- Reading the first OR as the nonbare operand also leaves the third
gate equal to raw line, whenever that OR carries the line trace. -/
theorem excludes_nonbare_first_wire
    (floor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) → 27 ≤ C.size)
    (p q : Fin 14) (d : lineBase p.val q.val .first = true)
    (o : Bool) (a b : Prior) (ha : validPrior a) (hb : validPrior b)
    (suf : List Remap.Gate) (ord : backwards suf 17)
    (out : Nat) (validOut : out<17+suf.length)
    (budget : (circuit ([firstGate p q,secondGate o a b,firstMark]++suf) out).size ≤ 27)
    (spec : ∀ x : Fin 14 → Bool,
      (circuit ([firstGate p q,secondGate o a b,firstMark]++suf) out).eval (List.ofFn x)=true ↔ fano x) :
    False := by
  let pre := [firstGate p q,secondGate o a b]
  let R := redirected 14 7 pre suf out
  have wOrd : backwards pre 14 := earlier_order p q o a b ha hb
  have pt (x : Fin 14 → Bool) := redirect_earlier_physical 14 7 pre suf wOrd ord
    (by change 7<16; decide) out validOut (List.ofFn x) (by simp)
  have contains : p.val = 7 ∨ q.val = 7 := by simpa [lineBase,src] using d
  have eq (x : Fin 14 → Bool) :
      R.eval (List.ofFn x) = (circuit (pre++firstMark::suf) out).eval (List.ofFn x) := by
    change (redirected 14 7 pre suf out).eval (List.ofFn x) = _
    rw [(pt x).2.2,Circuit.eval,wires,evaluate_append]
    let w := evaluate pre (List.ofFn x)
    change (evaluate suf (w ++ [w.getD 7 false])).getD out false =
      (evaluate suf (w ++ [value firstMark w])).getD out false
    have v7 : w.getD 7 false = x 7 := by
      dsimp only [w,pre]
      rw [second_values p q o a b ha hb x,getD_app _ _ 7 _ (by simp [beforeTwo])]
      unfold beforeTwo
      rw [getD_app _ _ 7 _ (by simp),getOfFn x 7 false (by decide)]
      rfl
    have v14 : w.getD 14 false = (x p || x q) := by
      dsimp only [w,pre]
      rw [second_values p q o a b ha hb x,getD_app _ _ 14 _ (by simp [beforeTwo])]
      unfold beforeTwo
      have ee := getD_end (List.ofFn x) (x p || x q) false
      simpa only [List.length_ofFn] using ee
    have rep : value firstMark w = w.getD 7 false := by
      change (w.getD 7 false && w.getD 14 false) = w.getD 7 false
      rw [v7,v14]
      rcases contains with hp | hq
      · rw [show p = (7 : Fin 14) from Fin.ext hp]
        cases x 7 <;> rfl
      · rw [show q = (7 : Fin 14) from Fin.ext hq]
        cases x 7 <;> cases x p <;> rfl
    rw [rep]
  have lb := floor R (pt (fun _ => false)).1 (by intro x; rw [eq]; exact spec x)
  have rs := (pt (fun _ => false)).2.1
  have orig : (circuit (pre++firstMark::suf) out).size = 3+suf.length := by
    simp [pre,Circuit.size,circuit]; omega
  change R.size = 2+suf.length at rs
  change (circuit (pre++firstMark::suf) out).size ≤ 27 at budget
  omega

end ProofLantern.Remap.ThirdClosed

namespace ProofLantern.CircuitBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private theorem fold_keeps (gs : List Gate) (w : List Bool)
    (i : Nat) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem primary_wire (C : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  exact fold_keeps C.gates x i hi

/-- Public wire semantics for genuine backward-read gates, without
a claim about gates outside the list or index-valid but forward reads. -/
theorem backwards_gate (C : Circuit) (x : List Bool) (j : Nat)
    (hj : j < C.gates.length)
    (back : ∀ i ∈ (gateAt C j).inputs, i < x.length + j) :
    (C.wires x).getD (x.length+j) false =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          (C.wires x).getD i false) := by
  let g := gateAt C j
  let w := (C.gates.take j).foldl step x
  let tail := C.gates.drop (j+1)
  have split : C.gates = C.gates.take j ++ g :: tail := by
    dsimp only [tail,g]
    rw [gateAt,List.getD_eq_getElem _ _ hj,List.cons_getElem_drop_succ,List.take_append_drop]
  have len : w.length = x.length+j := by
    dsimp only [w]
    rw [fold_length,List.length_take, min_eq_left (Nat.le_of_lt hj)]
  have wires : C.wires x = (g::tail).foldl step w := by
    change C.gates.foldl step x = _
    nth_rw 1 [split]
    rw [List.foldl_append]
  have ref (i : Nat) (hi : i < w.length) :
      (C.wires x).getD i false = w.getD i false := by
    rw [wires,fold_keeps _ _ _ hi]
  have hh : (C.wires x).getD (x.length+j) false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    rw [wires,List.foldl_cons,← len, fold_keeps _ _ _ (by simp [step])]
    simp [step]
  rw [hh]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (ref i (by rw [len]; exact back i hi)).symm


def gateIsOr : GateOp → Bool
  | .or => true
  | _ => false

def boolGate (o a b : Bool) : Bool := if o then a || b else a && b

theorem exact_binary_gate (n : Nat) (C : Circuit) (m : IsAO2 n C) (x : List Bool)
    (nx : x.length = n) (j : Nat) (hj : j < C.gates.length) :
    let a := opnd C j 0
    let b := opnd C j 1
    let w := (C.wires x)
    a < n+j ∧ b < n+j ∧
      w.getD (n+j) false =
        boolGate (gateIsOr (gateAt C j).op) (w.getD a false) (w.getD b false) := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem (l := C.gates) hj
  have ha := m.2.2 _ hmem
  have hor := m.1 _ hmem
  have rel := backwards_gate C x j hj (by simpa [nx] using m.2.1 j hj)
  rw [nx] at rel
  rcases q : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩ <;>
    simp [q] at ha
  have back := m.2.1 j hj
  have ba : a < n+j := back a (by simp [q])
  have bb : b < n+j := back b (by simp [q])
  refine ⟨by simpa [opnd,q] using ba,by simpa [opnd,q] using bb,?_⟩
  rcases hor with hh | hh <;>
    simpa [opnd,q,hh,GateOp.eval,gateIsOr,boolGate] using rel


private theorem step_pair (o a b da db pa pb : Bool)
    (ha : a = true ∨ da = true → pa = true)
    (hb : b = true ∨ db = true → pb = true) :
    boolGate o a b = true ∨
      (if o then da || db else (a && db) || (da && b)) = true →
      boolGate o pa pb = true := by
  cases o <;> cases a <;> cases b <;> cases da <;> cases db <;>
    cases pa <;> cases pb <;> simp_all [boolGate]

/-- Connect wire-level derivative soundness to the actual upstream list
evaluator and exact binary backward gate model. -/
theorem derivative_accepts_pair (n : Nat) (C : Circuit) (m : IsAO2 n C)
    (baseInput pairInput : List Bool) (hb : baseInput.length = n)
    (hp : pairInput.length = n) (delta : Nat → Bool)
    (leaves : ∀ i < n, baseInput.getD i false = true ∨ delta i = true →
       pairInput.getD i false = true)
    (recurrence : ∀ j < C.gates.length,
      let a := opnd C j 0
      let b := opnd C j 1
      let u := (C.wires baseInput)
      delta (n+j) =
        if gateIsOr (gateAt C j).op then delta a || delta b
        else (u.getD a false && delta b) || (delta a && u.getD b false))
    (i : Nat) (inRange : i < n+C.gates.length) :
    (C.wires baseInput).getD i false = true ∨ delta i = true →
    (C.wires pairInput).getD i false = true := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i < n
    · rw [primary_wire C pairInput i (by simpa [hp] using hi),
          primary_wire C baseInput i (by simpa [hb] using hi)]
      exact leaves i hi
    · let j := i - n
      have he : i = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      rw [he]
      obtain ⟨ha,hbnd,hwbase⟩ := exact_binary_gate n C m baseInput hb j hj
      obtain ⟨_,_,hwpair⟩ := exact_binary_gate n C m pairInput hp j hj
      have hr := recurrence j hj
      dsimp only at hr hwbase hwpair ha hbnd
      rw [hwbase,hwpair,hr]
      have hab := ih (opnd C j 0) (by omega) (by omega)
      have hbb := ih (opnd C j 1) (by omega) (by omega)
      exact step_pair _ _ _ _ _ _ _ hab hbb

end ProofLantern.CircuitBridge


namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.ThirdShape

/-- For a genuine third bare mark rejecting the line singleton, the other
operand cannot be primary or the first OR. It is the second gate's output. -/
theorem actual_third_other_is_wire15
    (C : Circuit) (m : IsAO2 14 C) (ok : 2<C.gates.length)
    (first : (gateAt C 0).op = GateOp.or) (mark : (gateAt C 2).op = GateOp.and)
    (d : Nat → Bool) (seeded : ∀ i<14, d i = decide (i=7))
    (d14 : d 14 = (d (opnd C 0 0) || d (opnd C 0 1)))
    (other : Nat) (different : other≠7)
    (operands : Pair (opnd C 2 0) (opnd C 2 1) 7 other)
    (traced : d other = true)
    (miss : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=7)))).getD 16 false = false) :
    other=15 := by
  let w := List.ofFn fun i : Fin 14 => decide (i.val=7)
  let v := fun i => (C.wires w).getD i false
  have wl : w.length=14 := by simp [w]
  have get (i : Nat) (h : i<14) : v i = decide (i=7) := by
    unfold v
    rw [ProofLantern.CircuitBridge.primary_wire C w i (by rw [wl]; exact h)]
    exact getOfFn _ _ _ h
  have line : v 7 = true := by rw [get _ (by decide)]; rfl
  obtain ⟨b0,b1,ev⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m w wl 2 ok
  have bl : other<16 := by
    rcases operands with ⟨l,r⟩ | ⟨l,r⟩ <;> omega
  have pl : 14≤other := by
    by_cases h : other < 14
    · have q := traced
      rw [seeded other h] at q
      exact False.elim (different (decide_eq_true_eq.mp q))
    · omega
  by_cases h : other = 14
  · have t : d 14 = true := h ▸ traced
    rw [d14,Bool.or_eq_true] at t
    obtain ⟨a0,a1,ex⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m w wl 0 (by omega)
    have orTrue : v 14 = true := by
      change (C.wires w).getD (14+0) false = true
      rw [ex,first]
      change (v (opnd C 0 0) || v (opnd C 0 1)) = true
      rw [Bool.or_eq_true]
      rcases t with t | t
      · rw [seeded _ (by omega)] at t
        rw [decide_eq_true_eq.mp t]
        exact Or.inl line
      · rw [seeded _ (by omega)] at t
        rw [decide_eq_true_eq.mp t]
        exact Or.inr line
    have vExit : v 16 = true := by
      change (C.wires w).getD (14+2) false = true
      rw [ev,mark]
      change (v (opnd C 2 0) && v (opnd C 2 1)) = true
      rcases operands with ⟨l,r⟩ | ⟨l,r⟩
      · rw [l,r,h,line,orTrue]; rfl
      · rw [l,r,h,line,orTrue]; rfl
    exact False.elim (Bool.noConfusion (miss.symm.trans vExit))
  · omega

end ProofLantern.Remap.ThirdClosed

namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.ThirdShape

def decode (i : Nat) : Prior := if i=14 then .first else .raw i

theorem decode_index (i : Nat) : index (decode i) = i := by
  by_cases h : i=14
  · subst i; rfl
  · simp [decode,h,index]

theorem decode_valid (i : Nat) (h : i<15) : validPrior (decode i) := by
  by_cases e : i=14
  · subst i; trivial
  · simp only [decode,ite_eq_right e,validPrior]
    omega

theorem first_prefix_reads (C : Circuit) (m : IsAO2 14 C) (j0 : 0<C.gates.length)
    (p q : Fin 14) (pq : opnd C 0 0 = p.val) (qq : opnd C 0 1 = q.val)
    (first : (gateAt C 0).op = GateOp.or)
    (x : Fin 14 → Bool) (i : Nat) (h : i<15) :
    (C.wires (List.ofFn x)).getD i false = src p.val q.val (fn x) (decode i) := by
  by_cases e : i=14
  · subst i
    have g := (ProofLantern.CircuitBridge.exact_binary_gate 14 C m (List.ofFn x)
      (by simp) 0 j0).2.2
    change (C.wires (List.ofFn x)).getD (14+0) false = _
    rw [g,first,pq,qq]
    rw [ProofLantern.CircuitBridge.primary_wire _ _ _ (by simp),
        ProofLantern.CircuitBridge.primary_wire _ _ _ (by simp)]
    rfl
  · have lt : i<14 := by omega
    rw [ProofLantern.CircuitBridge.primary_wire _ _ _ (by simpa using lt)]
    simp [decode,e,src,fn]

/-- Checked decode of the actual two physical earlier wires and the
posted first-order recurrence into the small structural classification. -/
theorem actual_second_classifies
    (C : Circuit) (m : IsAO2 14 C) (ok : 1<C.gates.length)
    (p q : Fin 14) (p0 : opnd C 0 0 = p.val) (p1 : opnd C 0 1 = q.val)
    (distinctFirst : p.val≠q.val) (firstOr : (gateAt C 0).op = GateOp.or)
    (sep : opnd C 1 0 ≠ opnd C 1 1)
    (d : Nat → Bool) (dSeed : ∀ i<14, d i = decide (i=7))
    (d0 : d 14 = (d (opnd C 0 0) || d (opnd C 0 1)))
    (d1 : d 15 =
      (if ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op
        then d (opnd C 1 0) || d (opnd C 1 1)
        else let wb := C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))
             (wb.getD (opnd C 1 0) false && d (opnd C 1 1)) ||
             (d (opnd C 1 0) && wb.getD (opnd C 1 1) false)))
    (nonBase : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))).getD 15 false = false)
    (nonLine : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=7)))).getD 15 false = false)
    (trace : d 15 = true) :
    let a := decode (opnd C 1 0)
    let b := decode (opnd C 1 1)
    secondValue p.val q.val (ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op)
      a b (fun i => decide (i=0)) = false ∧
    secondValue p.val q.val (ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op)
      a b (fun i => decide (i=7)) = false ∧
    secondDelta p.val q.val (ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op) a b = true ∧
    ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op = false ∧
      (a=.raw 7 ∨ b=.raw 7 ∨ Canonical p.val q.val a b) := by
  let o := ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op
  let a := decode (opnd C 1 0)
  let b := decode (opnd C 1 1)
  have aNe : a≠b := by
    intro h
    have r := congrArg index h
    simp only [a,b,decode_index] at r
    exact sep r
  have rep (s : Nat) (x : Fin 14 → Bool) (h : s<15) :
      (C.wires (List.ofFn x)).getD s false =
        src p.val q.val (fn x) (decode s) :=
    first_prefix_reads C m (by omega) p q p0 p1 firstOr x s h
  have raw (k s : Nat) (hs : s<15) (hk : k<14) :
      src p.val q.val (fn (fun i : Fin 14 => decide (i.val=k))) (decode s) =
      src p.val q.val (fun i => decide (i=k)) (decode s) := by
    cases e : decode s
    · rename_i i
      have lt : i<14 := by
        have q := decode_valid s hs
        rw [e] at q
        exact q
      change fn (fun j : Fin 14 => decide (j.val=k)) i = decide (i=k)
      exact getOfFn _ _ _ lt
    · unfold src
      rw [fnGet _ p,fnGet _ q]
  have dd (s : Nat) (h : s<15) : d s = lineBase p.val q.val (decode s) := by
    by_cases e : s=14
    · subst s
      rw [d0,p0,p1,dSeed _ p.isLt,dSeed _ q.isLt]
      rfl
    · rw [dSeed _ (by omega)]
      simp [decode,e,lineBase,src]
  have bounds := ProofLantern.CircuitBridge.exact_binary_gate 14 C m (List.ofFn (fun _ : Fin 14 => false))
    (by simp) 1 ok
  have evalTest (k : Nat) (hk : k<14) :
      (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=k)))).getD 15 false =
        secondValue p.val q.val o a b (fun i => decide (i=k)) := by
    let x := fun i : Fin 14 => decide (i.val=k)
    have eb := (ProofLantern.CircuitBridge.exact_binary_gate 14 C m (List.ofFn x) (by simp) 1 ok).2.2
    change (C.wires (List.ofFn x)).getD (14+1) false = _
    rw [eb,rep _ x bounds.1,rep _ x bounds.2.1,raw _ _ bounds.1 hk,raw _ _ bounds.2.1 hk]
    rfl
  have z := (evalTest 0 (by decide)).symm.trans nonBase
  have l := (evalTest 7 (by decide)).symm.trans nonLine
  have ds : secondDelta p.val q.val o a b = true := by
    rw [d1] at trace
    dsimp only at trace
    rw [dd _ bounds.1,dd _ bounds.2.1,
      rep _ (fun i : Fin 14 => decide (i.val=0)) bounds.1,
      rep _ (fun i : Fin 14 => decide (i.val=0)) bounds.2.1,
      raw 0 _ bounds.1 (by decide),raw 0 _ bounds.2.1 (by decide)] at trace
    exact trace
  exact ⟨z,l,ds,classification p.val q.val distinctFirst o a b aNe z l ds⟩

end ProofLantern.Remap.ThirdClosed


namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap.Upstream

def swapped (g : Remap.Gate) : Remap.Gate := ⟨g.isOr,g.right,g.left⟩

theorem swapped_value (g : Remap.Gate) (w : List Bool) :
    value (swapped g) w = value g w := by
  obtain ⟨isOr,a,b⟩ := g
  cases isOr <;> simp [swapped,value,applyGate,Bool.or_comm,Bool.and_comm]

theorem swapped_preserves (pre suf : List Remap.Gate) (g : Remap.Gate)
    (out : Nat) (x : List Bool) :
    (circuit (pre++swapped g::suf) out).eval x =
      (circuit (pre++g::suf) out).eval x := by
  unfold Circuit.eval
  rw [wires,wires,evaluate_append,evaluate_append]
  change (evaluate suf ((evaluate pre x) ++ [value (swapped g) (evaluate pre x)])).getD out false =
    (evaluate suf ((evaluate pre x) ++ [value g (evaluate pre x)])).getD out false
  rw [swapped_value]

theorem take_three_actual (C : Circuit) (real : 2<C.gates.length) :
    ∃ t : List PEqualNP.CircuitLowerBounds.Gate,
      C.gates = [gateAt C 0,gateAt C 1,gateAt C 2]++t := by
  rcases h : C.gates with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩ <;> simp [h] at real
  exact ⟨t,by simp [gateAt,h]⟩

theorem encoded_first_three (C : Circuit) (m : IsAO2 14 C) (real : 2<C.gates.length) :
    ∃ t : List Remap.Gate, backwards t 17 ∧
      C = circuit ([unpack (gateAt C 0),unpack (gateAt C 1),unpack (gateAt C 2)]++t) C.output := by
  obtain ⟨t,ht⟩ := take_three_actual C real
  let r := fun _ : Nat => false
  have e := (original_exact 14 C m r).symm
  rw [tag_first,ht,List.map_append] at e
  have b := original_backwards 14 C m r
  rw [tag_first,ht,List.map_append] at b
  exact ⟨t.map unpack,b.2.2.2.2.2.2,e⟩

end ProofLantern.Remap.ThirdClosed


namespace ProofLantern.Remap.ThirdClosed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.Remap.TypedThird ProofLantern.ThirdShape

private theorem unpack_fields (C : Circuit) (j : Nat) :
    unpack (gateAt C j) = ⟨ProofLantern.CircuitBridge.gateIsOr (gateAt C j).op,
      opnd C j 0, opnd C j 1⟩ := by
  unfold unpack opnd
  cases (gateAt C j).op <;> rfl

/-- Complete actual third-position cut given the independently proved
singleton-line rejection consequence of ordinary minimum. -/
theorem actual_no_third_mark
    (floor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) → 27 ≤ C.size)
    (C : Circuit) (m : IsAO2 14 C) (sz : C.size≤27)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x)
    (output : C.output < 14+C.gates.length)
    (real : 2<C.gates.length) (firstOr : (gateAt C 0).op = GateOp.or)
    (markAnd : (gateAt C 2).op = GateOp.and)
    (sep0 : opnd C 0 0 ≠ opnd C 0 1) (sep1 : opnd C 1 0 ≠ opnd C 1 1)
    (other : Nat) (oneBare : Pair (opnd C 2 0) (opnd C 2 1) 7 other)
    (oneOther : other≠7)
    (d : Nat → Bool) (seed : ∀ i<14, d i=decide (i=7))
    (d0 : d 14=(d (opnd C 0 0) || d (opnd C 0 1)))
    (d1 : d 15 =
      (if ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op
        then d (opnd C 1 0) || d (opnd C 1 1)
        else let wb := C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))
             (wb.getD (opnd C 1 0) false && d (opnd C 1 1)) ||
             (d (opnd C 1 0) && wb.getD (opnd C 1 1) false)))
    (trace : d other=true)
    (nonBase : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))).getD other false = false)
    (miss : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=7)))).getD 16 false = false) :
    False := by
  have is15 := actual_third_other_is_wire15 C m real firstOr markAnd d seed d0 other oneOther oneBare trace miss
  subst other
  let line : List Bool := List.ofFn fun i : Fin 14 => decide (i.val=7)
  have len : line.length=14 := by simp [line]
  have base7 : (C.wires line).getD 7 false = true := by
    rw [ProofLantern.CircuitBridge.primary_wire C line 7 (by rw [len]; decide)]
    exact getOfFn _ _ _ (by decide)
  have nonLine : (C.wires line).getD 15 false = false := by
    have e := (ProofLantern.CircuitBridge.exact_binary_gate 14 C m line len 2 real).2.2
    change (C.wires line).getD (14+2) false = false at miss
    rw [e,markAnd] at miss
    rcases oneBare with ⟨a,b⟩ | ⟨a,b⟩
    · rw [a,b,base7] at miss
      exact miss
    · rw [a,b,base7] at miss
      simpa [ProofLantern.CircuitBridge.boolGate,ProofLantern.CircuitBridge.gateIsOr] using miss
  obtain ⟨a0,b0,_⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m line len 0 (by omega)
  obtain ⟨a1,b1,_⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m line len 1 (by omega)
  let p : Fin 14 := ⟨opnd C 0 0,a0⟩
  let q : Fin 14 := ⟨opnd C 0 1,b0⟩
  let a := decode (opnd C 1 0)
  let b := decode (opnd C 1 1)
  let o := ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op
  have av := decode_valid _ a1
  have bv := decode_valid _ b1
  have unequal : a≠b := by
    intro h
    apply sep1
    simpa only [a,b,decode_index] using congrArg index h
  obtain ⟨suf,ord,layout⟩ := encoded_first_three C m real
  have u0 : unpack (gateAt C 0) = firstGate p q := by rw [unpack_fields,firstOr]; rfl
  have u1 : unpack (gateAt C 1) = secondGate o a b := by
    unfold o a b secondGate
    rw [unpack_fields,decode_index,decode_index]
  rw [u0,u1] at layout
  let base := circuit ([firstGate p q,secondGate o a b,lastMark]++suf) C.output
  have size : C.size = 3+suf.length := by
    have e := congrArg Circuit.size layout
    simp [Circuit.size,circuit] at e
    change C.gates.length = 3+suf.length
    omega
  have valid : C.output < 17+suf.length := by
    unfold Circuit.size at size
    omega
  have sBase : base.size≤27 := by
    have e : base.size = 3+suf.length := by simp [base,Circuit.size,circuit]; omega
    omega
  have eval (x : Fin 14 → Bool) : base.eval (List.ofFn x)=C.eval (List.ofFn x) := by
    have e := congrArg (fun r => r.eval (List.ofFn x)) layout
    rcases oneBare with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · have u : unpack (gateAt C 2) = lastMark := by rw [unpack_fields,markAnd,h0,h1]; rfl
      rw [u] at e
      exact e.symm
    · have u : unpack (gateAt C 2) = swapped lastMark := by rw [unpack_fields,markAnd,h0,h1]; rfl
      rw [u] at e
      exact (swapped_preserves [firstGate p q,secondGate o a b] suf lastMark C.output (List.ofFn x)).symm.trans e.symm
  have z := actual_second_classifies C m (by omega) p q rfl rfl sep0 firstOr sep1 d seed d0 d1 nonBase nonLine trace
  exact excludes_nonbare_second_wire floor p q sep0 o a b av bv unequal z.1 z.2.1 z.2.2.1
    suf ord C.output valid sBase (by intro x; exact (eval x) ▸ spec x)

end ProofLantern.Remap.ThirdClosed


namespace ProofLantern.CircuitBridge
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
private theorem monotone_bit (o ba bb pa pb : Bool)
    (ha : ba = true → pa = true) (hb : bb = true → pb = true) :
    boolGate o ba bb = true → boolGate o pa pb = true := by
  cases o <;> cases ba <;> cases bb <;> cases pa <;> cases pb <;>
    simp_all [boolGate]

theorem monotone_wires (n : Nat) (C : Circuit) (m : IsAO2 n C)
    (x y : List Bool) (nx : x.length = n) (ny : y.length = n)
    (leaves : ∀ i < n, x.getD i false = true → y.getD i false = true)
    (i : Nat) (hi : i < n+C.gates.length) :
    (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hx : i < n
    · rw [primary_wire C x i (by simpa [nx] using hx),
          primary_wire C y i (by simpa [ny] using hx)]
      exact leaves i hx
    · let j := i-n
      have he : i = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      rw [he]
      obtain ⟨ha,hb,hcx⟩ := exact_binary_gate n C m x nx j hj
      obtain ⟨_,_,hcy⟩ := exact_binary_gate n C m y ny j hj
      rw [hcx,hcy]
      exact monotone_bit _ _ _ _ _
        (ih (opnd C j 0) (by omega) (by omega))
        (ih (opnd C j 1) (by omega) (by omega))


end ProofLantern.CircuitBridge
namespace ProofLantern.Remap.Restore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap ProofLantern.Remap.Upstream

def edge (x : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true

def fanoStar (x : Fin 14 → Bool) : Bool := (x 0 || x 1) || x 3

def restoreLine (x : Fin 14 → Bool) (i : Fin 14) : Bool :=
  if i.val = 7 then x i && fanoStar x else x i

def restorePref : List Remap.Gate :=
  [⟨true,0,1⟩,⟨true,14,3⟩,⟨false,7,15⟩]

def restoreMap : List Nat :=
  List.ofFn fun i : Fin 14 => if i.val = 7 then 16 else i.val

theorem flagged_edge (x : Fin 14 → Bool) (h : restoreLine x 7 = true) : edge x := by
  change (x 7 && ((x 0 || x 1) || x 3)) = true at h
  rw [Bool.and_eq_true,Bool.or_eq_true,Bool.or_eq_true] at h
  obtain ⟨hl,hp⟩ := h
  rcases hp with (p0 | p1) | p3
  · exact ⟨0,0,Or.inl rfl,p0,hl⟩
  · exact ⟨1,0,Or.inr (Or.inl rfl),p1,hl⟩
  · exact ⟨3,0,Or.inr (Or.inr rfl),p3,hl⟩

theorem restore_target (x : Fin 14 → Bool) :
    (restoreLine x 7 = true ∨ edge (restoreLine x)) ↔ edge x := by
  constructor
  · rintro (h | ⟨p,l,inc,hp,hl⟩)
    · exact flagged_edge x h
    · refine ⟨p,l,inc,?_,?_⟩
      · have hv : (Fin.castAdd 7 p).val ≠ 7 := by
          change p.val ≠ 7; exact Nat.ne_of_lt p.isLt
        simpa only [restoreLine,ite_eq_right hv] using hp
      · by_cases e : (Fin.natAdd 7 l).val = 7
        · rw [restoreLine,ite_eq_left e,Bool.and_eq_true] at hl
          exact hl.1
        · simpa only [restoreLine,ite_eq_right e] using hl
  · rintro ⟨p,l,inc,hp,hl⟩
    by_cases z : l = 0
    · subst l
      left
      change (x 7 && ((x 0 || x 1) || x 3)) = true
      have hp' : p = 0 ∨ p = 1 ∨ p = 3 := by simpa using inc
      rcases hp' with h | h | h <;> subst p
      · change x 0 = true at hp; change x 7 = true at hl; simp [hp,hl]
      · change x 1 = true at hp; change x 7 = true at hl; simp [hp,hl]
      · change x 3 = true at hp; change x 7 = true at hl; simp [hp,hl]
    · right
      refine ⟨p,l,inc,?_,?_⟩
      · have hp0 : (Fin.castAdd 7 p).val ≠ 7 := by
          change p.val ≠ 7; exact Nat.ne_of_lt p.isLt
        simpa only [restoreLine,ite_eq_right hp0] using hp
      · have hl0 : (Fin.natAdd 7 l).val ≠ 7 := by
          change 7+l.val ≠ 7
          have : l.val ≠ 0 := fun h => z (Fin.ext h)
          omega
        simpa only [restoreLine,ite_eq_right hl0] using hl


private theorem restore_initial (x : Fin 14 → Bool) :
    Agree restoreMap (List.ofFn (restoreLine x)) (evaluate restorePref (List.ofFn x)) := by
  let w := List.ofFn x
  let o := x 0 || x 1
  let a := w ++ [o]
  let b := a ++ [fanoStar x]
  let c := b ++ [x 7 && fanoStar x]
  have wl : w.length = 14 := by simp [w]
  have al : a.length = 15 := by simp [a,wl]
  have bl : b.length = 16 := by simp [b,al]
  have cl : c.length = 17 := by simp [c,bl]
  have h0 : value ⟨true,0,1⟩ w = o := by
    change (w.getD 0 false || w.getD 1 false) = o
    dsimp only [w]
    rw [getOfFn x 0 false (by decide),getOfFn x 1 false (by decide)]
    rfl
  have h1 : value ⟨true,14,3⟩ a = fanoStar x := by
    change (a.getD 14 false || a.getD 3 false) = fanoStar x
    have ea : a.getD 14 false = o := by
      have e := getD_end w o false
      rw [wl] at e
      exact e
    rw [ea,getD_app w [o] 3 false (by rw [wl]; decide)]
    dsimp only [w]
    rw [getOfFn x 3 false (by decide)]
    rfl
  have h2 : value ⟨false,7,15⟩ b = (x 7 && fanoStar x) := by
    change (b.getD 7 false && b.getD 15 false) = _
    have ea : b.getD 15 false = fanoStar x := by
      have e := getD_end a (fanoStar x) false
      rw [al] at e
      exact e
    rw [ea,getD_app a [fanoStar x] 7 false (by rw [al]; decide),
      getD_app w [o] 7 false (by rw [wl]; decide)]
    dsimp only [w]
    rw [getOfFn x 7 false (by decide)]
    rfl
  have e : evaluate restorePref (List.ofFn x) = c := by
    change evaluate [⟨true,14,3⟩,⟨false,7,15⟩] (w ++ [value ⟨true,0,1⟩ w]) = _
    rw [h0]
    change evaluate [⟨false,7,15⟩] (a ++ [value ⟨true,14,3⟩ a]) = _
    rw [h1]
    change b ++ [value ⟨false,7,15⟩ b] = c
    rw [h2]
  rw [e]
  refine ⟨by simp [restoreMap],?_⟩
  intro i hi
  have ilt : i < 14 := by simpa using hi
  rw [show restoreMap.getD i 0 = (if i=7 then 16 else i) from getOfFn _ i 0 ilt,
    getOfFn (restoreLine x) i false ilt]
  by_cases h : i = 7
  · subst i
    change 16 < c.length ∧ c.getD 16 false = restoreLine x 7
    have ee := getD_end b (x 7 && fanoStar x) false
    rw [bl] at ee
    exact ⟨by rw [cl]; decide,ee⟩
  · rw [ite_eq_right h]
    refine ⟨by rw [cl]; omega,?_⟩
    rw [getD_app b [x 7 && fanoStar x] i false (by rw [bl]; omega),
      getD_app a [fanoStar x] i false (by rw [al]; omega),
      getD_app w [o] i false (by rw [wl]; omega)]
    dsimp only [w]
    rw [getOfFn x i false ilt]
    simp [restoreLine,h]


/-- The ordinary 27-gate Fano lower bound implies a 24-gate lower bound
for the saturated target. Restore the three incident edges by replacing
the bare line with the AND of that line and its three-neighbor OR. -/
theorem saturated_floor (ordinaryFloor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x) → 27 ≤ C.size)
    (C : Circuit) (model : IsAO2 14 C)
    (validOutput : C.output < 14+C.gates.length)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ x 7 = true ∨ edge x) :
    24 ≤ C.size := by
  let noRemove : Nat → Bool := fun _ => false
  let gs := tag noRemove 0 C.gates
  let r := rebuild 7 gs 17 restoreMap
  let R := circuit (restorePref ++ r.2) (r.1.getD C.output 0)
  have glen : gs.length = C.gates.length := tag_length _ _ _
  have oe : circuit (gs.map Prod.fst) C.output = C := original_exact 14 C model noRemove
  have rr (x : Fin 14 → Bool) : IsAO2 14 R ∧
      R.size + (gs.filter Prod.snd).length = 3 + C.size ∧
      R.eval (List.ofFn x) = C.eval (List.ofFn (restoreLine x)) := by
    let w := List.ofFn (restoreLine x)
    let z := List.ofFn x
    have nl : w.length = 14 := by simp [w]
    have zl : z.length = 14 := by simp [z]
    have pref : backwards restorePref 14 := by
      change 0<14 ∧ 1<14 ∧ 14<15 ∧ 3<15 ∧ 7<16 ∧ 15<16 ∧ True
      decide
    have fl : 7 < (evaluate restorePref z).length := by rw [evaluate_length,zl]; decide
    have valid : admissible ((evaluate restorePref z).getD 7 false) gs w := by
      apply admissible_from_values
      · rw [nl]; exact original_backwards 14 C model noRemove
      · intro j hj sel
        have k := tag_selected noRemove 0 C.gates j hj
        have h : false = true := k.symm.trans sel
        cases h
    have out : C.output < (executeOriginal gs w).length := by
      rwa [executeOriginal_length,nl,glen]
    have q := remap_with_prefix 14 7 C.output restorePref gs restoreMap w z zl pref
      (restore_initial x) fl valid out
    rw [oe] at q
    have cnt := q.2.1
    rw [glen] at cnt
    exact ⟨q.1,cnt,q.2.2⟩
  have hr : 27 ≤ R.size := by
    apply ordinaryFloor R (rr (fun _ => false)).1
    intro x
    rw [(rr x).2.2,spec]
    exact restore_target x
  have count := (rr (fun _ => false)).2.1
  omega


theorem value_fold_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih]
    simp
    omega

theorem actual_value_length (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length+C.gates.length :=
  value_fold_length C.gates w

theorem saturated_output_valid (C : Circuit)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ x 7 = true ∨ edge x) :
    C.output < 14+C.gates.length := by
  have h := (spec (fun _ => true)).mpr (Or.inl rfl)
  unfold Circuit.eval at h
  have len : (C.wires (List.ofFn (fun _ : Fin 14 => true))).length = 14+C.gates.length := by
    rw [actual_value_length]; simp
  by_cases valid : C.output < 14+C.gates.length
  · exact valid
  · rw [List.getD_eq_default _ _ (by rw [len]; omega)] at h
    simp at h

theorem saturated_by_sub (x : Fin 14 → Bool) :
    edge (fanoSub x) ↔ x 7 = true ∨ edge x := by
  cases h : x 7 with
  | false =>
    have es : fanoSub x = x := by
      funext i
      simp [fanoSub,h]
    rw [es]
    simp
  | true =>
    have e : edge (fanoSub x) := by
      refine ⟨0,0,Or.inl rfl,?_,?_⟩
      · change fanoSub x 0 = true
        simp [fanoSub,h]
      · change fanoSub x 7 = true
        simpa [fanoSub] using h
    exact ⟨fun _ => Or.inl rfl,fun _ => e⟩

/-- Five verified literal aliases would exclude a 27-gate candidate
using the ordinary lower bound and the checked physical transforms. -/
theorem mask_cap_four (ordinaryFloor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x) → 27 ≤ C.size)
    (C : Circuit) (m : IsAO2 14 C) (budget : C.size ≤ 27)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x)
    (outValid : C.output < 14 + C.gates.length)
    (remove : Nat → Bool)
    (aliases : ∀ x : Fin 14 → Bool, ∀ j < C.gates.length, remove j = true →
      (C.wires (List.ofFn (fanoSub x))).getD (14+j) false = x 7) :
    ((tag remove 0 C.gates).filter Prod.snd).length ≤ 4 := by
  obtain ⟨R,shape,size,evaluation⟩ := remap_arbitrary_fano C m remove outValid aliases
  have newSpec (x : Fin 14 → Bool) :
      R.eval (List.ofFn x) = true ↔ x 7 = true ∨ edge x := by
    rw [evaluation,spec]
    exact saturated_by_sub x
  have lo := saturated_floor ordinaryFloor R shape (saturated_output_valid R newSpec) newSpec
  omega

end ProofLantern.Remap.Restore


namespace ProofLantern.Remap.AliasRows

def minOn (i : Fin 14) : Bool := decide (i.val=7)

end ProofLantern.Remap.AliasRows

namespace ProofLantern.Remap.Minimum

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open ProofLantern.Remap.Upstream ProofLantern.Remap.Restore ProofLantern.Remap.AliasRows

def identityMap : List Nat := List.ofFn fun i : Fin 14 => i.val

private theorem identity_agree (x : Fin 14 → Bool) :
    Agree identityMap (List.ofFn x) (List.ofFn x) := by
  refine ⟨by simp [identityMap],?_⟩
  intro i hi
  have v : i < 14 := by simpa using hi
  have e : identityMap.getD i 0 = i := getOfFn _ _ _ v
  rw [e]
  exact ⟨hi,rfl⟩

private theorem can_delete_literal (C : Circuit) (m : IsAO2 14 C)
    (validOutput : C.output < 14+C.gates.length)
    (j : Nat) (hj : j < C.gates.length)
    (certified : ∀ x : Fin 14 → Bool, (C.wires (List.ofFn x)).getD (14+j) false = x 7) :
    ∃ R : Circuit, IsAO2 14 R ∧ R.size < C.size ∧
      ∀ x : Fin 14 → Bool, R.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let onlyJ := fun k : Nat => decide (k = j)
  let gs := tag onlyJ 0 C.gates
  let r := rebuild 7 gs 14 identityMap
  let R := circuit r.2 (r.1.getD C.output 0)
  have glen : gs.length = C.gates.length := tag_length _ _ _
  have je : j < gs.length := by rwa [glen]
  have tagj : gs[j].2 = true := by
    have e := tag_selected onlyJ 0 C.gates j je
    simpa only [onlyJ,Nat.zero_add,decide_true] using e
  have contained : gs[j] ∈ gs.filter Prod.snd := List.mem_filter.mpr ⟨List.getElem_mem je,tagj⟩
  have positive : 0 < (gs.filter Prod.snd).length := by
    cases l : gs.filter Prod.snd with
    | nil => simp [l] at contained
    | cons a as => simp
  have orig := original_exact 14 C m onlyJ
  have cert (x : Fin 14 → Bool) : IsAO2 14 R ∧ R.size < C.size ∧
      R.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    let w := List.ofFn x
    have wl : w.length = 14 := by simp [w]
    have v : 7 < w.length := by rw [wl]; decide
    have o : C.output < (executeOriginal gs w).length := by
      rwa [executeOriginal_length,wl,glen]
    have ord : backwards (gs.map Prod.fst) w.length := by
      rw [wl]; exact original_backwards 14 C m onlyJ
    have same : (executeOriginal gs w) = C.wires w := by
      rw [← original_wires gs C.output w,orig]
    have a : admissible (w.getD 7 false) gs w := by
      apply admissible_from_values _ _ _ ord
      intro k hk h
      have se := tag_selected onlyJ 0 C.gates k hk
      change gs[k].2 = onlyJ (0+k) at se
      rw [h,Nat.zero_add] at se
      have kj : k = j := decide_eq_true_eq.mp se.symm
      subst k
      rw [same,wl,getOfFn x 7 false (by decide)]
      exact certified x
    have c := remap_with_prefix 14 7 C.output [] gs identityMap w w wl
      (by trivial) (identity_agree x) v a o
    simp only [List.nil_append,List.length_nil,Nat.add_zero,Nat.zero_add] at c
    rw [orig] at c
    have size : R.size + (gs.filter Prod.snd).length = C.size := by
      have h := c.2.1
      rw [glen] at h
      exact h
    exact ⟨c.1,by omega,c.2.2⟩
  exact ⟨R,(cert (fun _ => false)).1,(cert (fun _ => false)).2.1,fun x => (cert x).2.2⟩

/-- If a bare-line AND accepts the singleton line, its output was the raw
line even without OR substitution. No size-27 minimum circuit can contain it. -/
theorem minimum_bare_rejects_singleton
    (ordinaryFloor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x) → 27 ≤ C.size)
    (C : Circuit) (m : IsAO2 14 C) (budget : C.size ≤ 27)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x)
    (outValid : C.output < 14 + C.gates.length)
    (j : Nat) (hj : j < C.gates.length) (marked : (gateAt C j).op = GateOp.and)
    (bare : opnd C j 0 = 7 ∨ opnd C j 1 = 7) :
    (C.wires (List.ofFn minOn)).getD (14+j) false = false := by
  cases s : (C.wires (List.ofFn minOn)).getD (14+j) false
  · rfl
  · have a (x : Fin 14 → Bool) : (C.wires (List.ofFn x)).getD (14+j) false = x 7 := by
      let w := List.ofFn x
      have wl : w.length = 14 := by simp [w]
      have read : (C.wires w).getD 7 false = x 7 := by
        rw [ProofLantern.CircuitBridge.primary_wire C w 7 (by rw [wl]; decide),getOfFn x 7 false (by decide)]
        rfl
      change (C.wires w).getD (14+j) false = x 7
      cases h : x 7
      · obtain ⟨_,_,ev⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m w wl j hj
        rw [ev,marked]
        rcases bare with e | e
        · rw [e,read,h]; rfl
        · rw [e,read,h]; simp [ProofLantern.CircuitBridge.gateIsOr,ProofLantern.CircuitBridge.boolGate]
      · apply ProofLantern.CircuitBridge.monotone_wires 14 C m (List.ofFn minOn) w
          (by simp) wl _ (14+j) (by omega) s
        intro i hi val
        rw [getOfFn _ i false hi] at val
        have eq : i = 7 := decide_eq_true_eq.mp val
        subst i
        change (List.ofFn x).getD 7 false = true
        rw [getOfFn x 7 false (by decide)]
        exact h
    obtain ⟨R,sound,smaller,rs⟩ := can_delete_literal C m outValid j hj a
    have lo := ordinaryFloor R sound (fun x => (rs x) ▸ spec x)
    omega


/-- An alleged earlier loss at index 1 has to use the first OR to trace
the bare line, so it would accept the line singleton and be redundant. -/
theorem no_bare_mark_at_second_gate
    (ordinaryFloor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x) → 27 ≤ C.size)
    (C : Circuit) (m : IsAO2 14 C) (budget : C.size ≤ 27)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ edge x)
    (outValid : C.output < 14 + C.gates.length) (real : 1 < C.gates.length)
    (firstOr : (gateAt C 0).op = GateOp.or)
    (secondAnd : (gateAt C 1).op = GateOp.and)
    (separate : opnd C 1 0 ≠ opnd C 1 1)
    (bare : opnd C 1 0 = 7 ∨ opnd C 1 1 = 7)
    (delta : Nat → Bool) (seed : ∀ i < 14, delta i = decide (i = 7))
    (trFirst : delta 14 = (delta (opnd C 0 0) || delta (opnd C 0 1)))
    (trL : delta (opnd C 1 0) = true) (trR : delta (opnd C 1 1) = true) :
    False := by
  let w := List.ofFn minOn
  have len : w.length = 14 := by simp [w]
  let value := fun i : Nat => (C.wires w).getD i false
  have primary (i : Nat) (hi : i < 14) : value i = decide (i = 7) := by
    dsimp only [value]
    rw [ProofLantern.CircuitBridge.primary_wire C w i (by rw [len]; exact hi),
      getOfFn minOn i false hi]
    rfl
  have vl : value 7 = true := by rw [primary 7 (by decide)]; rfl
  obtain ⟨s0,s1,e1⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m w len 1 real
  have other : opnd C 1 0 = 14 ∨ opnd C 1 1 = 14 := by
    rcases bare with h | h
    · right
      by_cases hh : opnd C 1 1 < 14
      · have q := trR
        rw [seed _ hh] at q
        exact False.elim (separate (h.trans (decide_eq_true_eq.mp q).symm))
      · omega
    · left
      by_cases hh : opnd C 1 0 < 14
      · have q := trL
        rw [seed _ hh] at q
        exact False.elim (separate ((decide_eq_true_eq.mp q).trans h.symm))
      · omega
  have d14 : delta 14 = true := by
    rcases other with h | h
    · rw [← h]; exact trL
    · rw [← h]; exact trR
  have z0 : 0 < C.gates.length := by omega
  obtain ⟨r0,r1,e0⟩ := ProofLantern.CircuitBridge.exact_binary_gate 14 C m w len 0 z0
  rw [trFirst,Bool.or_eq_true] at d14
  have v14 : value 14 = true := by
    change (C.wires w).getD (14+0) false = true
    rw [e0,firstOr]
    rcases d14 with h | h
    · rw [seed _ (by omega)] at h
      have q := decide_eq_true_eq.mp h
      change (value (opnd C 0 0) || value (opnd C 0 1)) = true
      rw [q,vl]
      rfl
    · rw [seed _ (by omega)] at h
      have q := decide_eq_true_eq.mp h
      change (value (opnd C 0 0) || value (opnd C 0 1)) = true
      rw [q,vl]
      simp
  have v15 : value 15 = true := by
    change (C.wires w).getD (14+1) false = true
    rw [e1,secondAnd]
    change (value (opnd C 1 0) && value (opnd C 1 1)) = true
    rcases bare with x | y <;> rcases other with u | v
    · omega
    · rw [x,v,vl,v14]; rfl
    · rw [y,u,v14,vl]; rfl
    · omega
  have neg := minimum_bare_rejects_singleton ordinaryFloor C m budget spec outValid 1 real secondAnd bare
  exact Bool.noConfusion (neg.symm.trans v15)

end ProofLantern.Remap.Minimum


namespace ProofLantern.Remap.ThirdClosed
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open ProofLantern.Remap.TypedThird ProofLantern.ThirdShape ProofLantern.Remap.Restore ProofLantern.Remap.Minimum

theorem actual_no_third_mark_from_floor
    (floor : ∀ C : Circuit, IsAO2 14 C →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x) → 27 ≤ C.size)
    (C : Circuit) (m : IsAO2 14 C) (sz : C.size≤27)
    (spec : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ fano x)
    (real : 2<C.gates.length) (firstOr : (gateAt C 0).op = GateOp.or)
    (markAnd : (gateAt C 2).op = GateOp.and)
    (sep0 : opnd C 0 0 ≠ opnd C 0 1) (sep1 : opnd C 1 0 ≠ opnd C 1 1)
    (other : Nat) (oneBare : Pair (opnd C 2 0) (opnd C 2 1) 7 other)
    (oneOther : other≠7)
    (d : Nat → Bool) (seed : ∀ i<14, d i=decide (i=7))
    (d0 : d 14=(d (opnd C 0 0) || d (opnd C 0 1)))
    (d1 : d 15 =
      (if ProofLantern.CircuitBridge.gateIsOr (gateAt C 1).op
        then d (opnd C 1 0) || d (opnd C 1 1)
        else let wb := C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))
             (wb.getD (opnd C 1 0) false && d (opnd C 1 1)) ||
             (d (opnd C 1 0) && wb.getD (opnd C 1 1) false)))
    (trace : d other=true)
    (nonBase : (C.wires (List.ofFn (fun i : Fin 14 => decide (i.val=0)))).getD other false = false)
    : False := by
  have bare : opnd C 2 0=7 ∨ opnd C 2 1=7 := by
    rcases oneBare with ⟨l,r⟩ | ⟨l,r⟩
    · exact Or.inl l
    · exact Or.inr r
  let allOn : Fin 14 → Bool := fun _ => true
  have hit := (spec allOn).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
  have output : C.output < 14+C.gates.length := by
    by_cases h : C.output < 14+C.gates.length
    · exact h
    · unfold Circuit.eval at hit
      rw [List.getD_eq_default _ _ (by rw [actual_value_length]; simp; omega)] at hit
      contradiction
  have miss := minimum_bare_rejects_singleton floor C m sz spec output 2 real markAnd bare
  exact actual_no_third_mark floor C m sz spec output real firstOr markAnd sep0 sep1 other oneBare oneOther
    d seed d0 d1 trace nonBase miss

end ProofLantern.Remap.ThirdClosed
