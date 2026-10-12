import Work.GCert.Scalar.Def

/-!
# (key: gx-scalar) The scalar check of a `gcert/1` certificate, whole or in segments (kernel terms)

Core Lean only.  The main phase is a list of items (`prog`): chunks of gates of `A`, the scatter,
chunks of gates of `B`.  `segCheck` replays a sublist of items from the first contents or from a
given state to a given state or to the final test; `scalCheck` is the whole in one evaluation;
`yCheck` is the y check (E4).  Soundness: `Work.GCert.Scalar.Main`.
-/

namespace GS
open SSC GXD

/-- structural equality of two tries, for the kernel -/
noncomputable def beqK : Trie → Trie → Bool :=
  Trie.rec (motive := fun _ => Trie → Bool)
    (fun x t' => Trie.rec (motive := fun _ => Bool) (fun x' => Nat.beq x x') (fun _ _ _ _ => false) t')
    (fun _ _ el er t' => Trie.rec (motive := fun _ => Bool) (fun _ => false)
      (fun l' r' _ _ => guard (el l') (er r')) t')

/-- a trie from the CHUNKED list of its non-zero leaves `(register, leaf)` (the states at the cuts) -/
noncomputable def loadK (d : Nat) (ls : List (List (Nat × Nat))) : Trie :=
  List.rec (motive := fun _ => Trie → Trie) (fun t => t)
    (fun l _ ih t => ih (List.rec (motive := fun _ => Trie → Trie) (fun t => t)
      (fun x _ ih2 t => ih2 (t.set x.1 x.2)) l t)) ls (Trie.mk d)

/-- the main phase as a list of items: chunks of gates of `A`, the scatter, chunks of gates of `B` -/
inductive Item where
  | cA (gs : List Gate)
  | scat
  | cB (gs : List Gate)

/-- the items of a certificate -/
def prog (c : Raw) : List Item := c.A.map Item.cA ++ (Item.scat :: c.B.map Item.cB)

section
variable (c : Raw) (p : SPar) (v2 nr tm K m2 rl : Nat)

noncomputable def gItem (it : Item) (tr : Trie) (k : Trie → Bool) : Bool :=
  Item.rec (motive := fun _ => Bool)
    (fun gs => gGates tm K m2 p.ux p.us p.uy c.v v2 (okAK c.v v2 nr) (fun _ => true) gs tr k)
    (gScat tm K m2 p.ux p.us p.uy c.v v2 (okSK c.v v2 nr) c.ret rl (scatRows c) c.v tr k)
    (fun gs => gGates tm K m2 p.ux p.us p.uy c.v v2 (okBK c.v v2 nr) (fun _ => true) gs tr k) it

noncomputable def gItems : List Item → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool)
    (fun tr k => k tr)
    (fun it _ ih tr k => gItem c p v2 nr tm K m2 rl it tr fun tr' => ih tr' k)

end

/-- **A segment of the scalar check** (E3, E5) for the sources `lo .. lo+n-1`: from the first
contents (`pre = none`) or from a given state, through the items, to a given state or to the
final test (`post = none`: x_t and y_t hold exactly source `t`). -/
noncomputable def segCheck (c : Raw) (p : SPar) (lo n : Nat) (pre : Option Trie) (items : List Item)
    (post : Option Trie) : Bool :=
  gPre c p lo n fun v2 nr hi tm K m2 => forceN (List.length c.ret) fun rl =>
    Option.rec (motive := fun _ => (Trie → Bool) → Bool)
      (fun k => gInit p.sw p.ux lo n 0 (Trie.mk p.d) k) (fun t k => k t) pre fun tr0 =>
        gItems c p v2 nr tm K m2 rl items tr0 fun tr3 =>
          Option.rec (motive := fun _ => Bool)
            (guard (gFin p.sw K m2 p.ux 0 lo hi tr3 c.v 0) (gFin p.sw K m2 p.uy c.v lo hi tr3 c.v 0))
            (fun t => beqK tr3 t) post

/-- **The scalar check** in one evaluation. -/
noncomputable def scalCheck (c : Raw) (p : SPar) (lo n : Nat) : Bool :=
  segCheck c p lo n none (prog c) none

/-- **The y check** (E4): the adds of `B` reading a y role, for the y roles `lo .. lo+n-1`. -/
noncomputable def yCheck (c : Raw) (p : SPar) (lo n : Nat) : Bool :=
  gPre c p lo n fun v2 nr hi tm K m2 =>
    gInit p.sw p.uy (Nat.add c.v lo) n 0 (Trie.mk p.d) fun tr0 =>
      gChunks tm K m2 p.ux p.us p.uy c.v v2 (okBK c.v v2 nr) (selY c.v v2) c.B tr0 fun tr3 =>
        gFin p.sw K m2 p.uy c.v lo hi tr3 c.v 0

end GS
