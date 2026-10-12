/-!
# Shared-sum checker (key: shared-sum-checker): the computable certificate checker

Core Lean only (no Mathlib).  Everything here is plain data and functions on `Nat`, written
with explicit recursors and raw `Nat.*` operations so that the KERNEL can evaluate it
(`by decide +kernel`) with as few reduction steps as possible.  Soundness is proved in
`Work.SharedSumChecker.Sound`.

## Certificate format (one labelled network on roles `0 .. 2^d - 1`)

* A LABEL of a role is one natural number `L` (stored as `enc L`, see below) packing a `Z/4`-valued quadratic form on
  `F_2^h` (the phase the role's frame applies at a Walsh address):
  bit `w*i` = `c0_i`, bit `K + w*i` = `c1_i`, bit `2K + w*i + j` = `B_ij`  (`K = w*h`),
  phase `Φ(L)(y) = ∏_i tint(y_i)^c0_i · sign(y_i)^c1_i · ∏_{i<j} sign(y_i y_j)^B_ij`.
  The zero label is the trivial frame.  Equal numbers give equal phases (that is all the
  soundness proof needs); a kernel move along the direction `z` (bit mask `< 2^h`) multiplies
  the phase by `tint(z·y)` and is the update `upd`; a free shift along `z` multiplies it by
  `sign(z·y)` and is `updS`.
* A PART is one role taking part in a gate, together with the frame change that brings it to
  the common label of the gate: `old r dirs sh` (role already used: `r` below the next unused
  role), `new r dirs sh` (first
  use: `r` must be the next unused role, whose label is zero), `stay r` (no frame change).
  `dirs` are the directions of the kernel moves (one PAID move each), `sh` one free shift.
* An OP is `bip srcs tgts coefs` (every part is brought to ONE common label, then
  `tgt_i += coef_ij * src_j` for all `i, j`), `copy s d` / `copyNew s d` (`d := s`, the copy
  takes the label of its source), `erase d` (`d := 0`), or `expect r e` (no action: the role `r`
  must currently have the stored label `e`).
* FINAL entries `(r, dirs, sh, e)`: role `r` makes a last frame change and must arrive at the
  label `e`; roles strictly increasing.
* `check p inits ops fins N = true` says: starting from the labels `inits` (roles
  `0 .. len-1`, all other roles at the zero label) every gate finds its parts at one common
  label, every final label is as declared, and the total number of kernel moves is `N`.
-/

namespace SSC

/-! ## kernel evaluation helpers -/

/-- evaluate a `Nat` to a literal before continuing -/
noncomputable def forceN {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun m _ => k (Nat.succ m)) n

/-- as `forceN`, failing on zero -/
noncomputable def forcePos (n : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun m _ => k (Nat.succ m)) n

/-- continue only if the test holds -/
noncomputable def guard (b : Bool) (k : Bool) : Bool := Bool.rec false k b

/-! ## parameters and packed labels -/

/-- `∑_{i<n} 2^(u*i)` -/
def rep (u : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => Nat.add (Nat.mul (Nat.pow 2 u) (rep u n)) 1

/-- `h` = dimension of the label space, `w` = digit width (`h < w`), `d` = depth of the
role table (`2^d` roles). -/
structure Par where
  h : Nat
  w : Nat
  d : Nat
  /-- `1`: every label also counts the kernel moves made so far (in its bits above `3*w*h`,
  so roles compared at a gate must have made the same number of moves); `0`: no count -/
  cnt : Nat

def Par.K (p : Par) : Nat := Nat.mul p.w p.h
def Par.K2 (p : Par) : Nat := Nat.mul 2 (Nat.mul p.w p.h)
def Par.K3 (p : Par) : Nat := Nat.mul 3 (Nat.mul p.w p.h)
def Par.hm (p : Par) : Nat := Nat.sub (Nat.pow 2 p.h) 1
def Par.km (p : Par) : Nat := rep (Nat.sub p.w 1) p.h
def Par.mm (p : Par) : Nat := rep p.w p.h
def Par.n (p : Par) : Nat := Nat.pow 2 p.d

/-- bit `i` of `z` (for `i < h`) moved to bit `w*i` -/
def spread (p : Par) (z : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.land z p.hm) p.km) p.mm

/-- label after one kernel move along `z` (`zh = spread p z`), move counter unchanged -/
def updX (p : Par) (L zh z : Nat) : Nat :=
  Nat.xor L (Nat.xor zh (Nat.xor (Nat.shiftLeft (Nat.land L zh) p.K)
    (Nat.shiftLeft (Nat.mul zh (Nat.land z p.hm)) p.K2)))

/-- label after one kernel move along `z` (`zh = spread p z`) -/
def upd (p : Par) (L zh z : Nat) : Nat :=
  Nat.add (updX p L zh z) (Nat.shiftLeft p.cnt p.K3)

/-- number of kernel moves recorded in a label (meaningful when `p.cnt = 1`) -/
def cntOf (p : Par) (L : Nat) : Nat := Nat.shiftRight L p.K3

/-- label after a free shift along `z` -/
def updS (p : Par) (L z : Nat) : Nat := Nat.xor L (Nat.shiftLeft (spread p z) p.K)

/-- Stored form of a label: the label shifted up by 64 bits, with a checksum in the low 64
bits.  (Only for speed: the kernel hashes a numeral by its low 64 bits, and labels that agree
there would collide in its caches.  The checksum has no meaning.) -/
def enc (L : Nat) : Nat := Nat.add (Nat.shiftLeft L 64) (Nat.mod L 18446744073709551615)
def dec (P : Nat) : Nat := Nat.shiftRight P 64

def updE (p : Par) (P z : Nat) : Nat := enc (upd p (dec P) (spread p z) z)
def updSE (p : Par) (P z : Nat) : Nat := enc (updS p (dec P) z)

/-- apply kernel moves along `dirs` (each direction must be nonzero), counting them -/
noncomputable def applyDirs (p : Par) (dirs : List Nat) :
    Nat → Nat → (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun P c k => k P c)
    (fun z _ ih P c k => Bool.rec (forceN (updE p P z) fun P' => ih P' (Nat.succ c) k) false
      (Nat.beq (Nat.land z p.hm) 0)) dirs

/-! ## the role table -/

inductive Trie where
  | leaf (v : Nat)
  | node (l r : Trie)

def Trie.mk : Nat → Trie
  | 0 => .leaf 0
  | d+1 => .node (Trie.mk d) (Trie.mk d)

/-- read (fails if the key is out of range) -/
noncomputable def Trie.getK (t : Trie) : Nat → (Nat → Bool) → Bool :=
  Trie.rec (motive := fun _ => Nat → (Nat → Bool) → Bool)
    (fun v key k => Nat.rec (motive := fun _ => Bool) (k v) (fun _ _ => false) key)
    (fun _ _ gl gr key k => Bool.rec (gr (Nat.shiftRight key 1) k) (gl (Nat.shiftRight key 1) k)
      (Nat.beq (Nat.land key 1) 0)) t

noncomputable def Trie.set (t : Trie) : Nat → Nat → Trie :=
  Trie.rec (motive := fun _ => Nat → Nat → Trie) (fun _ _ v => .leaf v)
    (fun l r sl sr key v => Bool.rec (.node l (sr (Nat.shiftRight key 1) v))
      (.node (sl (Nat.shiftRight key 1) v) r) (Nat.beq (Nat.land key 1) 0)) t

/-! ## certificates -/

/-- rational coefficient `± num / den` -/
structure Coef where
  neg : Bool
  num : Nat
  den : Nat

inductive Part where
  | old (r : Nat) (dirs : List Nat) (sh : Nat)
  | new (r : Nat) (dirs : List Nat) (sh : Nat)
  | stay (r : Nat)

def Part.role : Part → Nat
  | .old r _ _ => r
  | .new r _ _ => r
  | .stay r => r

inductive Op where
  | bip (srcs tgts : List Part) (coefs : List (List Coef))
  | copy (s d : Nat)
  | copyNew (s d : Nat)
  | erase (d : Nat)
  | expect (r : Nat) (e : Nat)

structure FinE where
  r : Nat
  dirs : List Nat
  sh : Nat
  e : Nat

/-- one part: its label after its frame change, the new table, the next unused role, the
move count -/
noncomputable def onePart (p : Par) (pt : Part) (t : Trie) (f c : Nat)
    (k : Nat → Trie → Nat → Nat → Bool) : Bool :=
  Part.rec (motive := fun _ => Bool)
    (fun r dirs sh => guard (Nat.ble (Nat.succ r) f) (t.getK r fun L0 =>
      applyDirs p dirs L0 c fun L1 c1 =>
        forceN (updSE p L1 sh) fun L => forceN c1 fun c2 => k L (t.set r L) f c2))
    (fun r dirs sh => guard (Nat.beq r f) (guard (Nat.ble (Nat.succ f) p.n)
      (applyDirs p dirs 0 c fun L1 c1 =>
        forceN (updSE p L1 sh) fun L => forceN c1 fun c2 =>
          forceN (Nat.succ f) fun f2 => k L (t.set r L) f2 c2)))
    (fun r => t.getK r fun L => k L t f c) pt

/-- all parts must arrive at the label `l` -/
noncomputable def partsK (p : Par) (l : Nat) (pts : List Part) :
    Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool)
    (fun t f c k => k t f c)
    (fun pt _ ih t f c k => onePart p pt t f c fun L t' f' c' =>
      guard (Nat.beq L l) (ih t' f' c' k)) pts

noncomputable def opK (p : Par) (op : Op) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun srcs tgts _ => List.rec (motive := fun _ => Bool) false
      (fun s0 rest _ => onePart p s0 t f c fun l t1 f1 c1 =>
        partsK p l rest t1 f1 c1 fun t2 f2 c2 => partsK p l tgts t2 f2 c2 k) srcs)
    (fun s d => guard (Nat.ble (Nat.succ d) f) (t.getK s fun L => k (t.set d L) f c))
    (fun s d => guard (Nat.beq d f) (guard (Nat.ble (Nat.succ f) p.n)
      (t.getK s fun L => forceN (Nat.succ f) fun f2 => k (t.set d L) f2 c)))
    (fun _ => k t f c)
    (fun r e => t.getK r fun L => guard (Nat.beq L e) (k t f c)) op

noncomputable def opsK (p : Par) (ops : List Op) :
    Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool)
    (fun t f c k => k t f c)
    (fun op _ ih t f c k => opK p op t f c fun t' f' c' => ih t' f' c' k) ops

/-- final frame changes (the table is only read); `lb` = lower bound for the next role -/
noncomputable def finK (p : Par) (t : Trie) (fs : List FinE) :
    Nat → Nat → (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun lb c k => k lb c)
    (fun fe _ ih lb c k => FinE.rec (motive := fun _ => Bool)
      (fun r dirs sh e => guard (Nat.ble lb r) (t.getK r fun L0 =>
        applyDirs p dirs L0 c fun L1 c1 => guard (Nat.beq (updSE p L1 sh) e)
          (forceN c1 fun c2 => forceN (Nat.succ r) fun lb2 => ih lb2 c2 k))) fe) fs

/-- initial labels of the roles `0, 1, ..` -/
noncomputable def initK (ls : List Nat) : Trie → Nat → (Trie → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → (Trie → Nat → Bool) → Bool)
    (fun t i k => k t i)
    (fun L _ ih t i k => forceN (Nat.succ i) fun i2 => ih (t.set i L) i2 k) ls

/-- ops given in chunks (avoids one huge list literal) -/
noncomputable def chunksK (p : Par) (cs : List (List Op)) :
    Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → Nat → (Trie → Nat → Nat → Bool) → Bool)
    (fun t f c k => k t f c)
    (fun ops _ ih t f c k => opsK p ops t f c fun t' f' c' => ih t' f' c' k) cs

noncomputable def finsK (p : Par) (t : Trie) (fs : List (List FinE)) :
    Nat → Nat → (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun lb c k => k lb c)
    (fun fl _ ih lb c k => finK p t fl lb c fun lb2 c2 => ih lb2 c2 k) fs

/-- **The checker.**  `inits` = labels of the roles `0 .. len-1` (all other roles start at the
zero label), `cs` = the ops (in chunks), `fs` = the final entries (in chunks),
`N` = total number of kernel moves. -/
noncomputable def check (p : Par) (inits : List Nat) (cs : List (List Op))
    (fs : List (List FinE)) (N : Nat) : Bool :=
  initK inits (Trie.mk p.d) 0 fun t0 f0 => guard (Nat.ble f0 p.n)
    (chunksK p cs t0 f0 0 fun t1 _ c1 => finsK p t1 fs 0 c1 fun _ c2 => Nat.beq c2 N)

end SSC
