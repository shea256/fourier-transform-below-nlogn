import Work.CarrierCheck.CCert

/-!
# (key: carrier-check) The kernel check of the scalar identity of a carrier circuit (functions)

Core Lean only.  ALL gates of the certificate (phase `A`, the scatter, phase `B`) are replayed,
in order, on the x-CONTENT of every role: the vector of the coefficients of the inputs `x_T` in
the value the role holds (helper slots are taken as zero at the start: their dirt is the
business of the invocation theorem).  A content vector is a pair `(P, N)` of natural numbers,
"positive part" and "negative part", each packing `v` digits of width `sw`:

    coefficient of x_T  =  (digit_T P - digit_T N) / unit,   unit = 1 for x roles and slots, 2 for y roles.

A gate `t += (± num/den) * s` adds `w` times the pair of `s` (exchanged if the sign is `-`) to the
pair of `t`, where `w = num` (`den = 1`) for a slot target and `w = 2 num / den` (`den ∈ {1, 2}`)
for a y target.  After EVERY addition all digits must be below `2^(sw-1)` (mask test), so no
carry ever crosses a digit.  At the end `P = N + 2 * 2^(sw * S)` must hold for every `y_S`:
its content is exactly `x_S`.  Soundness: `Work.CarrierCheck.ScalSound`.
-/

namespace SSC

/-- `acc + n * a`, by `n` additions; after every addition `acc &&& tm = 0` -/
noncomputable def addNC (tm a : Nat) (n : Nat) : Nat → (Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Bool) → Bool) (fun acc k => k acc)
    (fun _ ih acc k => forceN (Nat.add acc a) fun acc' =>
      guard (Nat.beq (Nat.land acc' tm) 0) (ih acc' k)) n

/-- sign and weight of a coefficient: `num` (`den = 1`) for a slot target, `2 num / den`
(`den = 1` or `2`) for a y target -/
noncomputable def wgtK (isY : Bool) (cf : Coef) (k : Bool → Nat → Bool) : Bool :=
  Coef.rec (motive := fun _ => Bool) (fun ng num den =>
    Bool.rec (motive := fun _ => Bool)
      (guard (Nat.beq den 1) (k ng num))
      (Bool.rec (motive := fun _ => Bool) (guard (Nat.beq den 1) (k ng (Nat.mul 2 num)))
        (k ng num) (Nat.beq den 2))
      isY) cf

/-- one gate `t += cf * s` (`s` below `y0`: not a y role; `t ≠ s`) -/
noncomputable def sAdd (tm y0 t s : Nat) (cf : Coef) (tP tN : Trie)
    (k : Trie → Trie → Bool) : Bool :=
  guard (Nat.ble (Nat.succ s) y0) (Bool.rec (motive := fun _ => Bool)
    (tP.getK s fun ps => tN.getK s fun ns => tP.getK t fun pt => tN.getK t fun nt =>
      wgtK (Nat.ble y0 t) cf fun ng w =>
        Bool.rec (motive := fun _ => Bool)
          (addNC tm ps w pt fun pt' => addNC tm ns w nt fun nt' => k (tP.set t pt') (tN.set t nt'))
          (addNC tm ns w pt fun pt' => addNC tm ps w nt fun nt' => k (tP.set t pt') (tN.set t nt'))
          ng)
    false (Nat.beq t s))

/-- the gates `t += c_j * src_j` of one target (missing coefficients are `1`) -/
noncomputable def sRow (tm y0 t : Nat) (srcs : List Part) :
    List Coef → Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => List Coef → Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun _ tP tN k => k tP tN)
    (fun s _ ih cfs tP tN k => List.rec (motive := fun _ => Bool)
      (sAdd tm y0 t s.role ⟨false, 1, 1⟩ tP tN fun tP' tN' => ih [] tP' tN' k)
      (fun cf cs _ => sAdd tm y0 t s.role cf tP tN fun tP' tN' => ih cs tP' tN' k) cfs) srcs

/-- all gates of a `bip` op, target by target -/
noncomputable def sGates (tm y0 : Nat) (srcs tgts : List Part) :
    List (List Coef) → Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => List (List Coef) → Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun _ tP tN k => k tP tN)
    (fun t _ ih rows tP tN k => List.rec (motive := fun _ => Bool)
      (sRow tm y0 t.role srcs [] tP tN fun tP' tN' => ih [] tP' tN' k)
      (fun row rs _ => sRow tm y0 t.role srcs row tP tN fun tP' tN' => ih rs tP' tN' k) rows) tgts

noncomputable def sOp (tm y0 : Nat) (op : Op) (tP tN : Trie) (k : Trie → Trie → Bool) : Bool :=
  Op.rec (motive := fun _ => Bool) (fun srcs tgts coefs => sGates tm y0 srcs tgts coefs tP tN k)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ _ => k tP tN) op

noncomputable def sOps (tm y0 : Nat) (ops : List Op) :
    Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun tP tN k => k tP tN)
    (fun op _ ih tP tN k => sOp tm y0 op tP tN fun tP' tN' => ih tP' tN' k) ops

noncomputable def sChunks (tm y0 : Nat) (cs : List (List Op)) :
    Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun tP tN k => k tP tN)
    (fun ops _ ih tP tN k => sOps tm y0 ops tP tN fun tP' tN' => ih tP' tN' k) cs

/-- the scatter row of the target role `t`: `t += coef * slot (ret k)` for its entries `(k, coef)` -/
noncomputable def sScatRow (tm y0 v : Nat) (ret : List Nat) (t : Nat) (l : List (Nat × Coef)) :
    Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun tP tN k => k tP tN)
    (fun x _ ih tP tN k => sAdd tm y0 t (Nat.add v (ret.getD x.1 0)) x.2 tP tN
      fun tP' tN' => ih tP' tN' k) l

/-- the scatter rows of the targets `t, t+1, ..` -/
noncomputable def sScat (tm y0 v : Nat) (ret : List Nat) (rows : List (List (Nat × Coef))) :
    Nat → Trie → Trie → (Trie → Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Trie → Trie → (Trie → Trie → Bool) → Bool)
    (fun _ tP tN k => k tP tN)
    (fun l _ ih t tP tN k => sScatRow tm y0 v ret t l tP tN fun tP' tN' =>
      forceN (Nat.succ t) fun t2 => ih t2 tP' tN' k) rows

/-- first contents: the role `i` (an x role) holds `x_i`, for `i, i+1, ..` (`n` of them) -/
noncomputable def sInitK (sw : Nat) (n : Nat) : Nat → Trie → (Trie → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun _ ih i t k => forceN (Nat.shiftLeft 1 (Nat.mul sw i)) fun b =>
      forceN (Nat.succ i) fun i2 => ih i2 (t.set i b) k) n

/-- at the end the y role `y0 + S` holds exactly `x_S` (two half units), for `S, S+1, ..` -/
noncomputable def sFinK (sw y0 : Nat) (tP tN : Trie) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih S => tP.getK (Nat.add y0 S) fun P => tN.getK (Nat.add y0 S) fun N =>
      guard (Nat.beq P (Nat.add N (Nat.shiftLeft 2 (Nat.mul sw S))))
        (forceN (Nat.succ S) ih)) n

/-- **The scalar check of a carrier certificate.** -/
noncomputable def CCert.scalarCheck (c : CCert) : Bool :=
  guard (decide (3 ≤ c.sw))
    (forceN (Nat.shiftLeft (rep c.sw c.v) (Nat.sub c.sw 1)) fun tm =>
      forceN (Nat.add c.v c.R) fun y0 =>
        sInitK c.sw c.v 0 (Trie.mk c.p.d) fun tP0 =>
          sChunks tm y0 c.A tP0 (Trie.mk c.p.d) fun tP1 tN1 =>
            sScat tm y0 c.v c.ret c.scat y0 tP1 tN1 fun tP2 tN2 =>
              sChunks tm y0 c.B tP2 tN2 fun tP3 tN3 => sFinK c.sw y0 tP3 tN3 c.v 0)

end SSC
