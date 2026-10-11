import Work.SharedSumChecker.PCert

/-!
# (key: combine) The label check of a certificate in SEGMENTS (definitions, core Lean only)

The label check `check p inits cs fs N` of `Work.SharedSumChecker.Check` is ONE kernel evaluation;
its memory grows with the number of kernel moves of the certificate (about 18 KB per move), which
is too much for h = 20 on a 16 GB machine.  Here the chunk list `cs` is cut in three segments and
each segment is checked by its own kernel evaluation, between EXPLICIT states of the checker
(role table, next unused role, move count):

* `segFirst p inits cs T F C`   from the initial labels, `cs` leads to the state `(T, F, C)`;
* `segMid p cs T0 F0 C0 T F C`  from the state `(T0, F0, C0)`, `cs` leads to the state `(T, F, C)`;
* `segLast p cs fs N T0 F0 C0`  from the state `(T0, F0, C0)`: `cs`, the final entries, the count.

`Work.Combine.Split` proves that the three together give `check p inits (csA ++ (csB ++ csC)) fs N`.
-/

namespace SSC

/-- structural equality of two role tables -/
noncomputable def Trie.beqK : Trie → Trie → Bool :=
  Trie.rec (motive := fun _ => Trie → Bool)
    (fun v t' => Trie.rec (motive := fun _ => Bool) (fun v' => Nat.beq v v') (fun _ _ _ _ => false) t')
    (fun _ _ el er t' => Trie.rec (motive := fun _ => Bool) (fun _ => false)
      (fun l' r' _ _ => guard (el l') (er r')) t')

/-- the state of the checker is `(T, F, C)` -/
noncomputable def stEqK (T : Trie) (F C : Nat) : Trie → Nat → Nat → Bool :=
  fun t f c => guard (Trie.beqK t T) (guard (Nat.beq f F) (Nat.beq c C))

noncomputable def segFirst (p : Par) (inits : List Nat) (cs : List (List Op)) (T : Trie) (F C : Nat) :
    Bool :=
  initK inits (Trie.mk p.d) 0 fun t0 f0 => guard (Nat.ble f0 p.n) (chunksK p cs t0 f0 0 (stEqK T F C))

noncomputable def segMid (p : Par) (cs : List (List Op)) (T0 : Trie) (F0 C0 : Nat) (T : Trie)
    (F C : Nat) : Bool :=
  chunksK p cs T0 F0 C0 (stEqK T F C)

noncomputable def segLast (p : Par) (cs : List (List Op)) (fs : List (List FinE)) (N : Nat)
    (T0 : Trie) (F0 C0 : Nat) : Bool :=
  chunksK p cs T0 F0 C0 fun t1 _ c1 => finsK p t1 fs 0 c1 fun _ c2 => Nat.beq c2 N

end SSC
