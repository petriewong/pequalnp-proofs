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
