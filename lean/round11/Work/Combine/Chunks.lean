import Work.Combine.XInvocation
import Work.Combine.Ranks
import Work.SharedSumChecker.Circ

/-!
# (key: combine) A checked certificate as a BLOCK route: one block per frame change

`Work.SharedSumChecker.Proj` (`Complete.path`) turns a contiguous part of a checked
micro-program into a unit-move path, one move per `dir` micro-op.  Here the same part is
cut into CHUNKS

* `blk r dirs`   the kernel moves `dirs` of ONE frame change of the role `r`: ONE block of
                 rank `dirs.length`;
* `gate t s c`   one addition gate;
* `skip ms`      micro-ops that do not move the projector label of any embedded role
                 (free shifts, `expect`s, moves of roles outside the embedding, and gates that
                 are deliberately left out when only the labels are followed),

and `Complete.xpath` shows that a chunk list is an exact block route (`XRoute`) for EVERY block
frame map (`XMap`), with price `rcost φ (chunksRanks cs)`: the list of the lengths of its
`blk` chunks.

Why a frame change is a legal block: a role of a complete certificate ends with projector `1`
after exactly `h` moves, so ALL its moves form one orthonormal basis (`Complete.base`), and the
moves of one frame change are a set of lines of that basis (`Complete.climb`).  Orthonormal
lines are linearly independent, which is what the block engine asks (`OBase.fam_indep`).

`Op.chunks`, `FinE.chunks` translate the ops and the final entries of a certificate; the roles
`v ≤ r < v + R` (the helper slots) are the embedded ones.  `Op.ranks`, `FinE.ranks` are the
block ranks read off the certificate text.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB Finset Matrix

/-! ## chunks -/

inductive Chunk where
  | blk (r : Nat) (dirs : List Nat)
  | gate (t s : Nat) (c : Coef)
  | skip (ms : List Micro)

def Chunk.micro : Chunk → List Micro
  | .blk r dirs => dirsM r dirs
  | .gate t s c => [.add t s c]
  | .skip ms => ms

/-- the rank of the block of a chunk (as a list: nothing for gates and skips) -/
def Chunk.ranks : Chunk → List Nat
  | .blk _ dirs => [dirs.length]
  | .gate _ _ _ => []
  | .skip _ => []

def chunksMicro (cs : List Chunk) : List Micro := cs.flatMap Chunk.micro
def chunksRanks (cs : List Chunk) : List Nat := cs.flatMap Chunk.ranks

theorem chunksMicro_nil : chunksMicro [] = [] := rfl
theorem chunksMicro_cons (ch : Chunk) (cs : List Chunk) :
    chunksMicro (ch :: cs) = ch.micro ++ chunksMicro cs := rfl
theorem chunksMicro_append (a b : List Chunk) :
    chunksMicro (a ++ b) = chunksMicro a ++ chunksMicro b := by
  simp [chunksMicro, List.flatMap_append]
theorem chunksRanks_nil : chunksRanks [] = [] := rfl
theorem chunksRanks_cons (ch : Chunk) (cs : List Chunk) :
    chunksRanks (ch :: cs) = ch.ranks ++ chunksRanks cs := rfl
theorem chunksRanks_append (a b : List Chunk) :
    chunksRanks (a ++ b) = chunksRanks a ++ chunksRanks b := by
  simp [chunksRanks, List.flatMap_append]

theorem chunksMicro_flatMap {ι : Type} (l : List ι) (f : ι → List Chunk) :
    chunksMicro (l.flatMap f) = l.flatMap (fun x => chunksMicro (f x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, chunksMicro_append, ih, List.flatMap_cons]

theorem chunksRanks_flatMap {ι : Type} (l : List ι) (f : ι → List Chunk) :
    chunksRanks (l.flatMap f) = l.flatMap (fun x => chunksRanks (f x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, chunksRanks_append, ih, List.flatMap_cons]

def isAdd : Micro → Bool
  | .add _ _ _ => true
  | _ => false

section
variable {ρ : Type}

/-- micro-ops that do not move the projector label of an embedded role -/
def quiet (emb : ρ → Nat) : Micro → Prop
  | .dir r _ => ∀ q, emb q ≠ r
  | .copy _ _ => False
  | _ => True

def Chunk.ok (emb : ρ → Nat) (unemb : Nat → ρ) : Chunk → Prop
  | .blk r _ => emb (unemb r) = r
  | .gate t s _ => emb (unemb t) = t ∧ emb (unemb s) = s
  | .skip ms => ∀ m ∈ ms, quiet emb m

/-- no gate chunk -/
def Chunk.noGate : Chunk → Prop
  | .gate _ _ _ => False
  | _ => True

/-- no addition hidden in a skip -/
def Chunk.noAdd : Chunk → Prop
  | .skip ms => ∀ m ∈ ms, isAdd m = false
  | _ => True

end

/-! ## labels along kernel moves -/

theorem runLab_dirsM (p : Par) (lab : Nat → Nat) (r : Nat) (dirs : List Nat) :
    runLab p lab (dirsM r dirs) = Function.update lab r (foldU p (lab r) dirs) := by
  induction dirs generalizing lab with
  | nil =>
    show lab = Function.update lab r (lab r)
    rw [Function.update_eq_self]
  | cons z zs ih =>
    show runLab p (stepLab p (.dir r z) lab) (dirsM r zs) = _
    rw [ih]
    show Function.update (Function.update lab r (upd p (lab r) (spread p z) z)) r
      (foldU p (Function.update lab r (upd p (lab r) (spread p z) z) r) zs) = _
    rw [Function.update_self, Function.update_idem]
    rfl

theorem cnt_foldU (p : Par) (hh : 0 < p.h) (hw : p.h < p.w) (hc : p.cnt = 1) (L : Nat)
    (dirs : List Nat) : cntOf p (foldU p L dirs) = cntOf p L + dirs.length := by
  induction dirs generalizing L with
  | nil => rfl
  | cons z zs ih =>
    show cntOf p (foldU p (upd p L (spread p z) z) zs) = _
    rw [ih, cnt_upd p hh hw, hc, List.length_cons]
    omega

section
variable {ρ : Type}

/-- quiet micro-ops leave the projector label and the move count of embedded roles alone -/
theorem Lb_quiet (p : Par) (hh : 0 < p.h) (hw : p.h < p.w) (emb : ρ → Nat) (ms : List Micro) :
    ∀ (lab : Nat → Nat), (∀ m ∈ ms, quiet emb m) → ∀ q, Lb p (runLab p lab ms (emb q)) = Lb p (lab (emb q)) := by
  induction ms with
  | nil => intro lab _ q; rfl
  | cons m ms ih =>
    intro lab hq q
    rw [runLab_cons, ih _ (fun m' h' => hq m' (List.mem_cons_of_mem _ h')) q]
    have hm := hq m (List.mem_cons_self ..)
    cases m with
    | dir r z =>
      have hne : emb q ≠ r := hm q
      simp only [stepLab, Function.update_of_ne hne]
    | shift r z =>
      by_cases e : emb q = r
      · simp only [stepLab, e, Function.update_self]
        show (⟨pmat p (updS p _ z), cntOf p (updS p _ z)⟩ : Lbl (Fin p.h)) = ⟨pmat p _, cntOf p _⟩
        rw [pmat_updS p hh hw, cnt_updS p hh hw]
      · simp only [stepLab, Function.update_of_ne e]
    | add _ _ _ => rfl
    | copy _ _ => exact False.elim hm
    | erase _ => rfl
    | expect _ _ => rfl

end

/-! ## the scalar matrix of a chunk list -/

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- product of the gate matrices of the gate chunks (later gates on the left) -/
noncomputable def matC (unemb : Nat → ρ) : List Chunk → Matrix ρ ρ ℚ
  | [] => 1
  | .gate t s c :: cs => matC unemb cs * addMat (unemb t) (unemb s) c.val
  | .blk _ _ :: cs => matC unemb cs
  | .skip _ :: cs => matC unemb cs

theorem matP_dirs (unemb : Nat → ρ) (r : Nat) (dirs : List Nat) (rest : List Micro) :
    matP unemb (dirsM r dirs ++ rest) = matP unemb rest := by
  induction dirs with
  | nil => rfl
  | cons z zs ih => exact ih

theorem matP_noAdd (unemb : Nat → ρ) (ms rest : List Micro) (h : ∀ m ∈ ms, isAdd m = false) :
    matP unemb (ms ++ rest) = matP unemb rest := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have ih' := ih (fun m' h' => h m' (List.mem_cons_of_mem _ h'))
    have hm := h m (List.mem_cons_self ..)
    cases m with
    | add _ _ _ => exact absurd hm (by simp [isAdd])
    | dir _ _ => exact ih'
    | shift _ _ => exact ih'
    | copy _ _ => exact ih'
    | erase _ => exact ih'
    | expect _ _ => exact ih'

/-- without additions hidden in skips, the chunk matrix is the matrix of the micro-program -/
theorem matC_eq_matP (unemb : Nat → ρ) (cs : List Chunk) (h : ∀ ch ∈ cs, ch.noAdd) :
    matC unemb cs = matP unemb (chunksMicro cs) := by
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    have ih' := ih (fun ch' h' => h ch' (List.mem_cons_of_mem _ h'))
    have hch := h ch (List.mem_cons_self ..)
    rw [chunksMicro_cons]
    cases ch with
    | blk r dirs =>
      show matC unemb cs = matP unemb (dirsM r dirs ++ chunksMicro cs)
      rw [matP_dirs, ih']
    | gate t s c =>
      show matC unemb cs * addMat (unemb t) (unemb s) c.val
        = matP unemb (chunksMicro cs) * addMat (unemb t) (unemb s) c.val
      rw [ih']
    | skip ms =>
      show matC unemb cs = matP unemb (ms ++ chunksMicro cs)
      rw [matP_noAdd unemb ms _ hch, ih']

/-- without gate chunks the chunk matrix is the identity -/
theorem matC_noGate (unemb : Nat → ρ) (cs : List Chunk) (h : ∀ ch ∈ cs, ch.noGate) :
    matC unemb cs = 1 := by
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    have ih' := ih (fun ch' h' => h ch' (List.mem_cons_of_mem _ h'))
    have hch := h ch (List.mem_cons_self ..)
    cases ch with
    | blk r dirs => exact ih'
    | gate t s c => exact False.elim hch
    | skip ms => exact ih'

variable {p : Par} {α : Type} [Fintype α] [DecidableEq α]

/-- **A chunk list of a complete certificate is an exact block route for every block frame
map**: one block of rank `dirs.length` per `blk` chunk, scalar map = the product of its gate
chunks. -/
theorem Complete.xpath {lab0 : Nat → Nat} {H0 : Nat → List Nat} {tot : List Micro} {emb : ρ → Nat}
    (C : Complete p lab0 H0 tot emb) (unemb : Nat → ρ) (hun : ∀ q, unemb (emb q) = q)
    (Xm : XMap (Fin p.h) α) (cs : List Chunk) :
    ∀ (a c : List Micro), tot = a ++ chunksMicro cs ++ c → (∀ ch ∈ cs, ch.ok emb unemb) →
      XRoute (fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P)
        (fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ chunksMicro cs) (emb q))).P)
        (actPoint (matC unemb cs)) (fun φ => rcost φ (chunksRanks cs)) := by
  induction cs with
  | nil =>
    intro a c _ _
    rw [chunksMicro_nil, List.append_nil]
    show XRoute _ _ (actPoint (1 : Matrix ρ ρ ℚ)) _
    rw [actPoint_one']
    exact XRoute.refl.cast (fun φ => rfl)
  | cons ch cs ih =>
    intro a c htot hok
    have hch := hok ch (List.mem_cons_self ..)
    have htot' : tot = (a ++ ch.micro) ++ chunksMicro cs ++ c := by
      rw [htot, chunksMicro_cons]; simp
    have ih' := ih (a ++ ch.micro) c htot' (fun ch' h' => hok ch' (List.mem_cons_of_mem _ h'))
    have eapp : a ++ chunksMicro (ch :: cs) = (a ++ ch.micro) ++ chunksMicro cs := by
      rw [chunksMicro_cons]; simp
    rw [eapp]
    cases ch with
    | blk r dirs =>
      have hr : emb (unemb r) = r := hch
      have hcl := C.climb (unemb r) a (dirsM r dirs) (chunksMicro cs ++ c)
        (by rw [htot']; simp [Chunk.micro])
      rw [hr] at hcl
      have hcnt : (Lb p (runLab p lab0 (a ++ dirsM r dirs) r)).d - (Lb p (runLab p lab0 a r)).d
          = dirs.length := by
        show cntOf p (runLab p lab0 (a ++ dirsM r dirs) r) - cntOf p (runLab p lab0 a r) = _
        rw [runLab_append, runLab_dirsM, Function.update_self, cnt_foldU p C.hh C.hw C.hc]
        omega
      have hst : XStep (unemb r) (Xm.Φ (Lb p (runLab p lab0 a (emb (unemb r)))).P)
          (Xm.Φ (Lb p (runLab p lab0 (a ++ dirsM r dirs) r)).P)
          (fun φ => bcost φ dirs.length) := by
        rw [hr]
        have h1 := (Xm.climb hcl) ρ (unemb r)
        rwa [hcnt] at h1
      have hstep := XRoute.on_role (fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P) (unemb r)
        _ hst
      have hs : Function.update (fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P) (unemb r)
          (Xm.Φ (Lb p (runLab p lab0 (a ++ dirsM r dirs) r)).P)
          = fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ dirsM r dirs) (emb q))).P := by
        funext q
        by_cases e : q = unemb r
        · rw [e, Function.update_self, hr]
        · rw [Function.update_of_ne e]
          have hne : emb q ≠ r := fun h => e (by rw [← hun q, h])
          rw [runLab_append, runLab_dirsM, Function.update_of_ne hne]
      rw [hs] at hstep
      refine ((hstep.trans ih').castg rfl).cast (fun φ => ?_)
      show bcost φ dirs.length + rcost φ (chunksRanks cs) = rcost φ ([dirs.length] ++ chunksRanks cs)
      rw [rcost_append, rcost_single]
    | gate t s cf =>
      obtain ⟨ht, hs'⟩ := hch
      have hokm : okMicro p (.add t s cf) (runLab p lab0 a) := by
        have h1 := C.hok
        rw [htot', List.append_assoc, List.append_assoc, Ok_append] at h1
        exact h1.2.1
      obtain ⟨_, _, hl⟩ := hokm
      have hsame : (fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ [Micro.add t s cf]) (emb q))).P)
          = fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P := by
        funext q; rw [runLab_append]; rfl
      change XRoute _ (fun q => Xm.Φ (Lb p (runLab p lab0 ((a ++ [Micro.add t s cf])
        ++ chunksMicro cs) (emb q))).P) _ _
      change XRoute (fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ [Micro.add t s cf]) (emb q))).P)
        _ _ _ at ih'
      rw [hsame] at ih'
      have hg : XRoute (fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P)
          (fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P)
          (actPoint (addMat (unemb t) (unemb s) cf.val)) (fun _ => 0) := by
        apply XRoute.gate
        intro i j hij
        by_cases hd : i = j
        · rw [hd]
        · have hc : i = unemb t ∧ j = unemb s := by
            by_contra hc
            apply hij
            simp [addMat, hd, hc]
          rw [hc.1, hc.2, ht, hs', hl]
      have h := hg.trans ih'
      show XRoute _ _ (actPoint (matC unemb cs * addMat (unemb t) (unemb s) cf.val)) _
      rw [actPoint_mul]
      refine h.cast (fun φ => ?_)
      show (0:ℝ) + rcost φ (chunksRanks cs) = rcost φ ([] ++ chunksRanks cs)
      rw [zero_add, List.nil_append]
    | skip ms =>
      have hq : ∀ m ∈ ms, quiet emb m := hch
      have hsame : (fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ ms) (emb q))).P)
          = fun q => Xm.Φ (Lb p (runLab p lab0 a (emb q))).P := by
        funext q
        rw [runLab_append, Lb_quiet p C.hh C.hw emb ms _ hq q]
      change XRoute (fun q => Xm.Φ (Lb p (runLab p lab0 (a ++ ms) (emb q))).P) _ _ _ at ih'
      rw [hsame] at ih'
      exact ih'

end

/-! ## the chunks of a certificate -/

/-- one frame change: a block if the role is a helper slot, otherwise nothing to do -/
def moveChunks (v R r : Nat) (dirs : List Nat) (sh : Nat) : List Chunk :=
  if v ≤ r ∧ r < v + R then [.blk r dirs, .skip [.shift r sh]]
  else [.skip (dirsM r dirs ++ [.shift r sh])]

theorem moveChunks_micro (v R r : Nat) (dirs : List Nat) (sh : Nat) :
    chunksMicro (moveChunks v R r dirs sh) = dirsM r dirs ++ [.shift r sh] := by
  unfold moveChunks
  split <;> simp [chunksMicro, Chunk.micro]

theorem moveChunks_ranks (v R r : Nat) (dirs : List Nat) (sh : Nat) :
    chunksRanks (moveChunks v R r dirs sh) = moveRanks v R r dirs := by
  unfold moveChunks moveRanks
  split <;> simp [chunksRanks, Chunk.ranks]

def Part.chunks (v R : Nat) : Part → List Chunk
  | .old r dirs sh => moveChunks v R r dirs sh
  | .new r dirs sh => moveChunks v R r dirs sh
  | .stay _ => []

theorem Part.chunks_micro (v R : Nat) (pt : Part) : chunksMicro (pt.chunks v R) = pt.micro := by
  cases pt with
  | old r dirs sh => exact moveChunks_micro v R r dirs sh
  | new r dirs sh => exact moveChunks_micro v R r dirs sh
  | stay r => rfl

theorem Part.chunks_ranks (v R : Nat) (pt : Part) : chunksRanks (pt.chunks v R) = pt.ranks v R := by
  cases pt with
  | old r dirs sh => exact moveChunks_ranks v R r dirs sh
  | new r dirs sh => exact moveChunks_ranks v R r dirs sh
  | stay r => rfl

/-- a gate micro-op as a chunk -/
def gateOf : Micro → Chunk
  | .add t s c => .gate t s c
  | m => .skip [m]

/-- the gates of an op: kept (`g = true`) or left out (`g = false`: only labels are followed) -/
def gateChunks (g : Bool) (ms : List Micro) : List Chunk :=
  if g then ms.map gateOf else [.skip ms]

theorem gateOf_micro (m : Micro) : (gateOf m).micro = [m] := by cases m <;> rfl
theorem gateOf_ranks (m : Micro) : (gateOf m).ranks = [] := by cases m <;> rfl

theorem gateChunks_micro (g : Bool) (ms : List Micro) : chunksMicro (gateChunks g ms) = ms := by
  unfold gateChunks
  cases g
  · simp [chunksMicro, Chunk.micro]
  · simp only [if_true]
    induction ms with
    | nil => rfl
    | cons m ms ih => rw [List.map_cons, chunksMicro_cons, gateOf_micro, ih]; rfl

theorem gateChunks_ranks (g : Bool) (ms : List Micro) : chunksRanks (gateChunks g ms) = [] := by
  unfold gateChunks
  cases g
  · simp [chunksRanks, Chunk.ranks]
  · simp only [if_true]
    induction ms with
    | nil => rfl
    | cons m ms ih => rw [List.map_cons, chunksRanks_cons, gateOf_ranks, ih]; rfl

def Op.chunks (v R : Nat) (g : Bool) : Op → List Chunk
  | .bip srcs tgts coefs =>
    (srcs ++ tgts).flatMap (Part.chunks v R) ++ gateChunks g (gatesM srcs tgts coefs)
  | .copy s d => [.skip [.copy s d]]
  | .copyNew s d => [.skip [.copy s d]]
  | .erase d => [.skip [.erase d]]
  | .expect r e => [.skip [.expect r e]]

theorem Op.chunks_micro (v R : Nat) (g : Bool) (op : Op) :
    chunksMicro (op.chunks v R g) = op.micro := by
  cases op with
  | bip srcs tgts coefs =>
    show chunksMicro ((srcs ++ tgts).flatMap (Part.chunks v R) ++ gateChunks g (gatesM srcs tgts coefs))
      = (srcs ++ tgts).flatMap Part.micro ++ gatesM srcs tgts coefs
    rw [chunksMicro_append, chunksMicro_flatMap, gateChunks_micro]
    congr 1
    exact List.flatMap_congr (fun pt _ => Part.chunks_micro v R pt)
  | copy s d => rfl
  | copyNew s d => rfl
  | erase d => rfl
  | expect r e => rfl

theorem Op.chunks_ranks (v R : Nat) (g : Bool) (op : Op) :
    chunksRanks (op.chunks v R g) = op.ranks v R := by
  cases op with
  | bip srcs tgts coefs =>
    show chunksRanks ((srcs ++ tgts).flatMap (Part.chunks v R) ++ gateChunks g (gatesM srcs tgts coefs))
      = (srcs ++ tgts).flatMap (Part.ranks v R)
    rw [chunksRanks_append, chunksRanks_flatMap, gateChunks_ranks, List.append_nil]
    exact List.flatMap_congr (fun pt _ => Part.chunks_ranks v R pt)
  | copy s d => rfl
  | copyNew s d => rfl
  | erase d => rfl
  | expect r e => rfl

def opsChunks (v R : Nat) (g : Bool) (ops : List Op) : List Chunk := ops.flatMap (Op.chunks v R g)

theorem opsChunks_micro (v R : Nat) (g : Bool) (ops : List Op) :
    chunksMicro (opsChunks v R g ops) = ops.flatMap Op.micro := by
  unfold opsChunks
  rw [chunksMicro_flatMap]
  exact List.flatMap_congr (fun op _ => Op.chunks_micro v R g op)

theorem opsChunks_ranks (v R : Nat) (g : Bool) (ops : List Op) :
    chunksRanks (opsChunks v R g ops) = opsRanks v R ops := by
  unfold opsChunks opsRanks
  rw [chunksRanks_flatMap]
  exact List.flatMap_congr (fun op _ => Op.chunks_ranks v R g op)

def FinE.chunks (v R : Nat) (fe : FinE) : List Chunk := moveChunks v R fe.r fe.dirs fe.sh
def finsChunks (v R : Nat) (fs : List FinE) : List Chunk := fs.flatMap (FinE.chunks v R)

theorem finsChunks_micro (v R : Nat) (fs : List FinE) :
    chunksMicro (finsChunks v R fs) = fs.flatMap FinE.micro := by
  unfold finsChunks
  rw [chunksMicro_flatMap]
  exact List.flatMap_congr (fun fe _ => moveChunks_micro v R fe.r fe.dirs fe.sh)

theorem finsChunks_ranks (v R : Nat) (fs : List FinE) :
    chunksRanks (finsChunks v R fs) = finsRanks v R fs := by
  unfold finsChunks finsRanks
  rw [chunksRanks_flatMap]
  exact List.flatMap_congr (fun fe _ => moveChunks_ranks v R fe.r fe.dirs fe.sh)

/-! ## validity of the chunks of a certificate -/

section
variable {ρ : Type} (emb : ρ → Nat) (unemb : Nat → ρ) (v R : Nat)
  (hin : ∀ r, v ≤ r → r < v + R → emb (unemb r) = r)
  (hout : ∀ q, v ≤ emb q ∧ emb q < v + R)
include hin hout

theorem moveChunks_ok (r : Nat) (dirs : List Nat) (sh : Nat) :
    ∀ ch ∈ moveChunks v R r dirs sh, ch.ok emb unemb := by
  intro ch hch
  unfold moveChunks at hch
  by_cases h : v ≤ r ∧ r < v + R
  · rw [if_pos h] at hch
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    rcases hch with rfl | rfl
    · exact hin r h.1 h.2
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rw [hm]; exact trivial
  · rw [if_neg h] at hch
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    rw [hch]
    intro m hm
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h1
      intro q hq
      exact h (hq ▸ hout q)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rw [h1]; exact trivial

theorem Op.chunks_ok (g : Bool) (op : Op) (hp : op.plain = true)
    (hg : g = true → ∀ m ∈ op.micro, segOK emb unemb m) :
    ∀ ch ∈ op.chunks v R g, ch.ok emb unemb := by
  intro ch hch
  cases op with
  | bip srcs tgts coefs =>
    rcases List.mem_append.mp hch with h1 | h1
    · obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp h1
      cases pt with
      | old r dirs sh => exact moveChunks_ok emb unemb v R hin hout r dirs sh ch hpt
      | new r dirs sh => exact moveChunks_ok emb unemb v R hin hout r dirs sh ch hpt
      | stay r => exact absurd hpt (by simp [Part.chunks])
    · unfold gateChunks at h1
      cases g
      · simp only [Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil, or_false] at h1
        rw [h1]
        intro m hm
        obtain ⟨t, _, s, _, cf, e⟩ := mem_gatesM _ _ _ _ hm
        rw [e]; exact trivial
      · simp only [if_true] at h1
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t, _, s, _, cf, e⟩ := mem_gatesM _ _ _ _ hm
        have hseg := hg rfl m (List.mem_append_right _ hm)
        rw [e] at hseg ⊢
        exact hseg
  | copy s d => exact absurd hp (by simp [Op.plain])
  | copyNew s d => exact absurd hp (by simp [Op.plain])
  | erase d => exact absurd hp (by simp [Op.plain])
  | expect r e =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hch
    rw [hch]
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [hm]; exact trivial

theorem opsChunks_ok (g : Bool) (ops : List Op) (hp : ∀ op ∈ ops, op.plain = true)
    (hg : g = true → ∀ m ∈ ops.flatMap Op.micro, segOK emb unemb m) :
    ∀ ch ∈ opsChunks v R g ops, ch.ok emb unemb := by
  intro ch hch
  obtain ⟨op, hop, hc⟩ := List.mem_flatMap.mp hch
  exact Op.chunks_ok emb unemb v R hin hout g op (hp op hop)
    (fun e m hm => hg e m (List.mem_flatMap.mpr ⟨op, hop, hm⟩)) ch hc

theorem finsChunks_ok (fs : List FinE) : ∀ ch ∈ finsChunks v R fs, ch.ok emb unemb := by
  intro ch hch
  obtain ⟨fe, _, hc⟩ := List.mem_flatMap.mp hch
  exact moveChunks_ok emb unemb v R hin hout fe.r fe.dirs fe.sh ch hc

end

theorem expM_quiet {ρ : Type} (emb : ρ → Nat) (l : List (Nat × Nat)) :
    ∀ m ∈ expM l, quiet emb m := by
  intro m hm
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
  exact trivial

theorem moveChunks_noGate (v R r : Nat) (dirs : List Nat) (sh : Nat) :
    ∀ ch ∈ moveChunks v R r dirs sh, ch.noGate := by
  intro ch hch
  unfold moveChunks at hch
  split at hch <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
  · rcases hch with rfl | rfl <;> exact trivial
  · rw [hch]; exact trivial

theorem moveChunks_noAdd (v R r : Nat) (dirs : List Nat) (sh : Nat) :
    ∀ ch ∈ moveChunks v R r dirs sh, ch.noAdd := by
  intro ch hch
  unfold moveChunks at hch
  split at hch <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
  · rcases hch with rfl | rfl
    · exact trivial
    · intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rw [hm]; rfl
  · rw [hch]
    intro m hm
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h1
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rw [h1]; rfl

/-- with the gates left out there is no gate chunk -/
theorem opsChunks_noGate (v R : Nat) (ops : List Op) :
    ∀ ch ∈ opsChunks v R false ops, ch.noGate := by
  intro ch hch
  obtain ⟨op, _, hc⟩ := List.mem_flatMap.mp hch
  cases op with
  | bip srcs tgts coefs =>
    rcases List.mem_append.mp hc with h1 | h1
    · obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp h1
      cases pt with
      | old r dirs sh => exact moveChunks_noGate v R r dirs sh ch hpt
      | new r dirs sh => exact moveChunks_noGate v R r dirs sh ch hpt
      | stay r => exact absurd hpt (by simp [Part.chunks])
    · simp only [gateChunks, Bool.false_eq_true, if_false, List.mem_cons, List.not_mem_nil,
        or_false] at h1
      rw [h1]; exact trivial
  | copy s d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; exact trivial
  | copyNew s d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; exact trivial
  | erase d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; exact trivial
  | expect r e =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; exact trivial

theorem finsChunks_noGate (v R : Nat) (fs : List FinE) :
    ∀ ch ∈ finsChunks v R fs, ch.noGate := by
  intro ch hch
  obtain ⟨fe, _, hc⟩ := List.mem_flatMap.mp hch
  exact moveChunks_noGate v R fe.r fe.dirs fe.sh ch hc

/-- with the gates kept no addition is hidden in a skip -/
theorem opsChunks_noAdd (v R : Nat) (ops : List Op) :
    ∀ ch ∈ opsChunks v R true ops, ch.noAdd := by
  intro ch hch
  obtain ⟨op, _, hc⟩ := List.mem_flatMap.mp hch
  cases op with
  | bip srcs tgts coefs =>
    rcases List.mem_append.mp hc with h1 | h1
    · obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp h1
      cases pt with
      | old r dirs sh => exact moveChunks_noAdd v R r dirs sh ch hpt
      | new r dirs sh => exact moveChunks_noAdd v R r dirs sh ch hpt
      | stay r => exact absurd hpt (by simp [Part.chunks])
    · simp only [gateChunks, if_true] at h1
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp h1
      cases m with
      | add t s c => exact trivial
      | dir r z => intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
      | shift r z => intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
      | copy s d => intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
      | erase d => intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
      | expect r e => intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
  | copy s d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
  | copyNew s d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
  | erase d =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl
  | expect r e =>
    simp only [Op.chunks, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; rw [hm]; rfl

/-! ## the transposed inverse of a chunk list -/

def Chunk.swap : Chunk → Chunk
  | .blk r dirs => .blk r dirs
  | .gate t s c => .gate s t c.negate
  | .skip ms => .skip (ms.map swapNeg)

theorem dirsM_swap (r : Nat) (dirs : List Nat) : (dirsM r dirs).map swapNeg = dirsM r dirs := by
  unfold dirsM
  rw [List.map_map]
  rfl

theorem chunksMicro_swap (cs : List Chunk) :
    chunksMicro (cs.map Chunk.swap) = (chunksMicro cs).map swapNeg := by
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    rw [List.map_cons, chunksMicro_cons, chunksMicro_cons, List.map_append, ih]
    congr 1
    cases ch with
    | blk r dirs => exact (dirsM_swap r dirs).symm
    | gate t s c => rfl
    | skip ms => rfl

theorem chunksRanks_swap (cs : List Chunk) : chunksRanks (cs.map Chunk.swap) = chunksRanks cs := by
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    rw [List.map_cons, chunksRanks_cons, chunksRanks_cons, ih]
    cases ch <;> rfl

theorem quiet_swap {ρ : Type} (emb : ρ → Nat) (m : Micro) (h : quiet emb m) : quiet emb (swapNeg m) := by
  cases m with
  | add t s c => exact trivial
  | dir _ _ => exact h
  | shift _ _ => exact h
  | copy _ _ => exact h
  | erase _ => exact h
  | expect _ _ => exact h

theorem Chunk.ok_swap {ρ : Type} (emb : ρ → Nat) (unemb : Nat → ρ) (ch : Chunk)
    (h : ch.ok emb unemb) : ch.swap.ok emb unemb := by
  cases ch with
  | blk r dirs => exact h
  | gate t s c => exact ⟨h.2, h.1⟩
  | skip ms =>
    intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    exact quiet_swap emb m' (h m' hm')

theorem Chunk.noAdd_swap (ch : Chunk) (h : ch.noAdd) : ch.swap.noAdd := by
  cases ch with
  | blk r dirs => exact trivial
  | gate t s c => exact trivial
  | skip ms =>
    intro m hm
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
    have h' := h m' hm'
    cases m' with
    | add t s c => exact absurd h' (by simp [isAdd])
    | dir _ _ => rfl
    | shift _ _ => rfl
    | copy _ _ => rfl
    | erase _ => rfl
    | expect _ _ => rfl

end SSC

#print axioms SSC.Complete.xpath
