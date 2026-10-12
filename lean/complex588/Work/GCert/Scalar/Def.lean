import Work.GCert.Data.Raw
import Work.CarrierCheck.ScalDef

/-!
# (key: gx-scalar) The kernel checks of the scalar half of a `gcert/1` certificate (functions)

Core Lean only.  The single adds of phase `A`, the scatter and phase `B` are replayed, in order,
on the CONTENT of every register for a batch of `n` sources `lo .. lo+n-1`: a pair `(P, N)` of
natural numbers packing `n` digits of width `sw` (ONE trie leaf `P + N * 2^(sw n)` per register),

    coefficient of source lo+T  =  (digit_T P - digit_T N) / unit,   unit = ux / uy / us (x, y, slot).

An add `t += (± num/den) s` has the digit weight `num * unit t / (den * unit s) = a / b` (reduced):
the pair of `s` is divided by `b` digit by digit (exactly: tested by `b` additions) and added `a`
times, exchanged for the sign `-`, to the pair of `t`; after every addition all digits are below
`2^(sw-1)` (mask test).  Inside the same replay: register bounds, `t ≠ s`, the
kinds of E3 (`okAK`, `okSK`, `okBK`), the sizes of the scatter.

* `scalCheck c p lo n`: sources = the x roles; at the end x_t and y_t hold exactly source `t`.
  `segCheck c p lo n pre items post` is one SEGMENT of it (states at the cuts given as tries).
* `yCheck c p lo n`: sources = the y roles, only the adds of `B` READING a y role; at the end
  y_t holds exactly its own source (the product of the y → y adds is the identity: E4).

Soundness: `Work.GCert.Scalar.Main`.
-/

namespace GS
open SSC GXD

/-- parameters of the scalar checks: trie depth, digit width, units of x / slot / y contents -/
structure SPar where
  d : Nat
  sw : Nat
  ux : Nat
  us : Nat
  uy : Nat

/-- unit of the register `r` (`v2 = 2 v`) -/
noncomputable def unitK (ux us uy v v2 r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) us uy (Nat.ble (Nat.succ r) v2)) ux (Nat.ble (Nat.succ r) v)

/-- kinds of phase A: x → slot, slot → slot -/
def okAK (v v2 nr t s : Nat) : Bool :=
  Nat.ble (Nat.succ t) nr && (Nat.ble (Nat.succ s) nr && (Nat.ble v2 t &&
    (Nat.ble (Nat.succ s) v || Nat.ble v2 s)))

/-- kinds of the scatter: slot → y -/
def okSK (v v2 nr t s : Nat) : Bool :=
  Nat.ble v t && (Nat.ble (Nat.succ t) v2 && (Nat.ble v2 s && Nat.ble (Nat.succ s) nr))

/-- kinds of phase B: into x only from x; a y role is read only by a y role -/
def okBK (v v2 nr t s : Nat) : Bool :=
  Nat.ble (Nat.succ t) nr && (Nat.ble (Nat.succ s) nr && ((Nat.ble v t || Nat.ble (Nat.succ s) v) &&
    (Nat.ble (Nat.succ s) v || (Nat.ble v2 s || (Nat.ble v t && Nat.ble (Nat.succ t) v2)))))

/-- the source is a y role -/
def selY (v v2 s : Nat) : Bool := Nat.ble v s && Nat.ble (Nat.succ s) v2

/-- exact division of a packed vector by `b`: the quotient `q` has small digits and `b` additions
of `q` give `X` back (so every digit of `X` is `b` times the digit of `q`) -/
noncomputable def gDiv (tm b X : Nat) (k : Nat → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (forceN (Nat.div X b) fun q => guard (Nat.beq (Nat.land q tm) 0)
      (addNC tm q b 0 fun r => guard (Nat.beq r X) (k q)))
    (k X) (Nat.beq b 1)

/-- read the leaf of `key`, let `f` compute its new value, continue with the updated trie
(ONE descent; fails if the key is out of range) -/
noncomputable def modK (t : Trie) : Nat → (Nat → (Nat → Bool) → Bool) → (Trie → Bool) → Bool :=
  Trie.rec (motive := fun _ => Nat → (Nat → (Nat → Bool) → Bool) → (Trie → Bool) → Bool)
    (fun v key f k => Nat.rec (motive := fun _ => Bool) (f v fun x => k (.leaf x))
      (fun _ _ => false) key)
    (fun l r ml mr key f k => Bool.rec (motive := fun _ => Bool)
      (mr (Nat.shiftRight key 1) f fun r' => k (.node l r'))
      (ml (Nat.shiftRight key 1) f fun l' => k (.node l' r))
      (Nat.beq (Nat.land key 1) 0)) t

/-- the leaf of the pair `(p, n)`: `p + n * 2^K` (`p < m2 = 2^K`, tested) -/
noncomputable def gEnc (K m2 p n : Nat) (kk : Nat → Bool) : Bool :=
  guard (Nat.ble (Nat.succ p) m2) (forceN (Nat.add p (Nat.shiftLeft n K)) kk)

/-- sign and digit weight `a / b` (reduced) of the add `t += co * s`:
`a / b = num * unit t / (den * unit s)` -/
noncomputable def gW (ux us uy v v2 t s : Nat) (co : Co) (k : Bool → Nat → Nat → Bool) : Bool :=
  Co.rec (motive := fun _ => Bool) (fun ng num den =>
    forceN (Nat.mul num (unitK ux us uy v v2 t)) fun A =>
      forceN (Nat.mul den (unitK ux us uy v v2 s)) fun B =>
        forceN (Nat.gcd A B) fun g => forceN (Nat.div A g) fun a => forceN (Nat.div B g) fun b =>
          guard (Nat.ble 1 B) (guard (Nat.ble 1 b)
            (guard (Nat.beq (Nat.mul a B) (Nat.mul A b)) (k ng a b)))) co

/-- the pair `(pt, nt)` receives `a / b` times the pair `(ps, ns)` (exchanged for the sign `-`);
`kk` receives the new leaf -/
noncomputable def gAcc (tm K m2 : Nat) (ng : Bool) (a b ps ns pt nt : Nat) (kk : Nat → Bool) : Bool :=
  gDiv tm b ps fun qp => gDiv tm b ns fun qn =>
    Bool.rec (motive := fun _ => Bool)
      (addNC tm qp a pt fun pt' => addNC tm qn a nt fun nt' => gEnc K m2 pt' nt' kk)
      (addNC tm qn a pt fun pt' => addNC tm qp a nt fun nt' => gEnc K m2 pt' nt' kk) ng

section
variable (tm K m2 ux us uy v v2 : Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)

/-- one add `t += co * s`; `ok` = the kind test, already a Boolean.  The digit weight is reduced
to `a / b` (`gW`); the pair of `s` is divided by `b` (exactly, `gDiv`) and added `a` times. -/
noncomputable def gAdd (t s : Nat) (co : Co) (ok : Bool) (tr : Trie) (k : Trie → Bool) : Bool :=
  guard ok (Bool.rec (motive := fun _ => Bool)
    (tr.getK s fun vs => modK tr t (fun vt kk =>
      gW ux us uy v v2 t s co fun ng a b =>
        gAcc tm K m2 ng a b (Nat.mod vs m2) (Nat.shiftRight vs K) (Nat.mod vt m2)
          (Nat.shiftRight vt K) kk) k)
    false (Nat.beq t s))

/-- the adds `t += co * s` of an `out` gate (source `s` selected) -/
noncomputable def gOut (s : Nat) : List (Nat × Co) → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun x _ ih tr k => gAdd tm K m2 ux us uy v v2 x.1 s x.2 (okf x.1 s) tr fun tr' => ih tr' k)

/-- the adds `t += co * s` of an `inn` gate (only the selected sources) -/
noncomputable def gInn (t : Nat) : List (Nat × Co) → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun x _ ih tr k => Bool.rec (motive := fun _ => Bool) (ih tr k)
      (gAdd tm K m2 ux us uy v v2 t x.1 x.2 (okf t x.1) tr fun tr' => ih tr' k) (sel x.1))

noncomputable def gGate (g : Gate) (tr : Trie) (k : Trie → Bool) : Bool :=
  Gate.rec (motive := fun _ => Bool)
    (fun _ s tgts _ => Bool.rec (motive := fun _ => Bool) (k tr)
      (gOut tm K m2 ux us uy v v2 okf s tgts tr k) (sel s))
    (fun _ t srcs => gInn tm K m2 ux us uy v v2 okf sel t srcs tr k) g

noncomputable def gGates : List Gate → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun g _ ih tr k => gGate tm K m2 ux us uy v v2 okf sel g tr fun tr' => ih tr' k)

noncomputable def gChunks : List (List Gate) → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun gs _ ih tr k => gGates tm K m2 ux us uy v v2 okf sel gs tr fun tr' => ih tr' k)

/-- the scatter row of the target register `t`: `t += co * (register of total k)` -/
noncomputable def gScatRow (ret : List (Nat × Nat)) (rl t : Nat) :
    List (Nat × Co) → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun x _ ih tr k => guard (Nat.ble (Nat.succ x.1) rl)
      (forceN (ret.getD x.1 (0, 0)).1 fun s =>
        gAdd tm K m2 ux us uy v v2 t s x.2 (okf t s) tr fun tr' => ih tr' k))

/-- the scatter rows of the targets `t, t+1, ..`; the last target is `v2 - 1` -/
noncomputable def gScat (ret : List (Nat × Nat)) (rl : Nat) :
    List (List (Nat × Co)) → Nat → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool)
    (fun t tr k => guard (Nat.beq t v2) (k tr))
    (fun l _ ih t tr k => gScatRow tm K m2 ux us uy v v2 okf ret rl t l tr fun tr' =>
      forceN (Nat.succ t) fun t2 => ih t2 tr' k)

end

/-- the star row of a port mask: `(k, inside)` if bit `k` is set, else `(k, outside)`, `k < h` -/
noncomputable def starRow (i o : Co) (p h : Nat) : List (Nat × Co) :=
  Nat.rec (motive := fun _ => List (Nat × Co)) []
    (fun k ih => (k, Bool.rec (motive := fun _ => Co) o i
      (Nat.beq (Nat.land (Nat.shiftRight p k) 1) 1)) :: ih) h

/-- the scatter rows of a certificate: the table, or the star rule expanded -/
noncomputable def scatRows (c : Raw) : List (List (Nat × Co)) :=
  Scat.rec (motive := fun _ => List (List (Nat × Co)))
    (fun i o => List.rec (motive := fun _ => List (List (Nat × Co))) []
      (fun p _ ih => starRow i o p c.h :: ih) c.ports)
    (fun rows => rows) c.scat

/-- first contents: the register `off + T` holds `u` at digit `T` (positive part), `T = i, i+1, ..`;
the low 64 bits hold the tag `u * tau T` (see `gPre`) -/
noncomputable def gInit (sw u off : Nat) (n : Nat) : Nat → Trie → (Trie → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun _ ih i t k => forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))) fun b =>
      forceN (Nat.succ i) fun i2 => ih i2 (t.set (Nat.add off i) b) k) n

/-- at the end the register `base + S` holds `u` at digit `S - lo` if `lo ≤ S < hi`, else nothing
(tags dropped) -/
noncomputable def gFin (sw K m2 u base lo hi : Nat) (tr : Trie) (cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih S => tr.getK (Nat.add base S) fun x =>
      guard (Nat.beq (Nat.shiftRight (Nat.mod x m2) 64)
          (Nat.add (Nat.shiftRight (Nat.shiftRight x K) 64) (Bool.rec (motive := fun _ => Nat) 0
            (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft u (Nat.mul sw (Nat.sub S lo)))
              (Nat.ble (Nat.succ S) hi)) (Nat.ble lo S))))
        (forceN (Nat.succ S) ih)) cnt

/-- every retained total sits in a slot register -/
noncomputable def retOKK (v2 nr : Nat) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => guard (Nat.ble v2 x.1) (guard (Nat.ble (Nat.succ x.1) nr) ih))

/-- the tests on the parameters; `k` receives `2 v`, the number of registers, `lo + n`, the mask,
`K = 64 + sw n`, `2^K`.

TAGS.  Every packed vector `V` (`n` digits of width `sw`) is stored as `V * 2^64 + tag`: the low
64 bits are a running weighted sum of the digits (weights `tau T`), added and divided along with
the digits.  They mean nothing; the mask keeps them below `2^63`, so they never carry into the
digits.  They are there because the kernel hashes a numeral by its low 64 bits: without them the
successive states collide in the kernel's caches and the run time is quadratic. -/
noncomputable def gPre (c : Raw) (p : SPar) (lo n : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  forceN (Nat.mul 2 c.v) fun v2 => forceN (Nat.add v2 c.R) fun nr => forceN (Nat.add lo n) fun hi =>
    forceN (Nat.pow 2 (Nat.sub p.sw 1)) fun half => forceN (Nat.add 64 (Nat.mul p.sw n)) fun K =>
      guard (Nat.ble 1 p.ux) (guard (Nat.ble 1 p.us) (guard (Nat.ble 1 p.uy)
        (guard (Nat.ble 1 p.sw) (guard (Nat.ble nr (Nat.pow 2 p.d)) (guard (Nat.ble hi c.v)
          (guard (Nat.ble (Nat.succ p.ux) half) (guard (Nat.ble (Nat.succ p.uy) half)
            (guard (Nat.ble (Nat.succ p.ux) 2147483648) (guard (Nat.ble (Nat.succ p.uy) 2147483648)
              (guard (retOKK v2 nr c.ret)
                (forceN (Nat.lor (Nat.shiftLeft (Nat.shiftLeft (rep p.sw n) (Nat.sub p.sw 1)) 64)
                    (Nat.pow 2 63)) fun tm =>
                  forceN (Nat.pow 2 K) fun m2 => k v2 nr hi tm K m2)))))))))))

end GS
