import Work.GCert.Labels.Def

/-!
# (key: gx-labels) The label check at the two ends and at the scatter: kernel term (core Lean only)

`endK p v ports rets S0 SA SF` (registers `x_t = t`, `y_t = v + t`, slot `q = 2 v + q`;
`S0`, `SA`, `SF` = states at the start, at the scatter, at the end; `rets` = retained registers):

* shape: `1 ≤ h`, `S0` has depth `d`, `n ≤ 2^d`, `2 v ≤ n`, `ports.length = v`, frame id 0 has
  dimension 0;
* port `u` of `t`: `u < 2^h - 1` (a vector, not all-ones), odd weight; `x_t` starts at a frame of
  dimension 1 that contains `u` and ends at dimension `h`; `y_t` starts and stands at the scatter
  at frame id 0, and ends at dimension `h - 1` in a frame all of whose digits are orthogonal to
  `u` (ONE packed parity fold `parsK`);
* every slot starts at frame id 0 and ends at dimension `h`;
* every retained register stands at the scatter at a frame of dimension `> 0`.
-/

namespace GLab
open SSC GXD

/-- XOR over `q < h` of `(Y >>> q) &&& O`: bit `i` of the result is the parity of the bits
`i .. i+h-1` of `Y` (for the bits `i` of `O`) -/
noncomputable def parsK (h O Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun q ih => Nat.xor ih (Nat.land (Nat.shiftRight Y q) O)) h

noncomputable def portsK (p : Par) (hm Oh sh v : Nat) (S0 SA SF : Trie) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq t v)
    (fun u _ ih t =>
      guard (Nat.ble (Nat.succ u) hm) <|
      guard (Nat.beq (parsK p.h 1 u) 1) <|
      S0.getK t fun a => p.tab.getK a fun ca =>
      guard (Nat.beq (Nat.land ca 255) 1) <|
      guard (elimT p.h hm 1 (Nat.shiftRight ca sh) u) <|
      S0.getK (Nat.add v t) fun a0 => guard (Nat.beq a0 0) <|
      SA.getK (Nat.add v t) fun a1 => guard (Nat.beq a1 0) <|
      SF.getK t fun b => p.tab.getK b fun cb => guard (Nat.beq (Nat.land cb 255) p.h) <|
      SF.getK (Nat.add v t) fun y => p.tab.getK y fun cy =>
      guard (Nat.beq (Nat.succ (Nat.land cy 255)) p.h) <|
      guard (Nat.beq (parsK p.h Oh (Nat.land (Nat.shiftRight cy sh) (Nat.mul u Oh))) 0) <|
      forceN (Nat.succ t) ih)

noncomputable def slotsK (p : Par) (v2 : Nat) (S0 SF : Trie) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun q ih => S0.getK (Nat.add v2 q) fun a => guard (Nat.beq a 0) <|
      SF.getK (Nat.add v2 q) fun b => p.tab.getK b fun cb =>
      guard (Nat.beq (Nat.land cb 255) p.h) ih)

noncomputable def retsK (p : Par) (SA : Trie) : List Nat → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => SA.getK r fun a => p.tab.getK a fun ca =>
      guard (Nat.ble 1 (Nat.land ca 255)) ih)

/-- **the label check at the ends and at the scatter** (see the file header) -/
noncomputable def endK (p : Par) (v : Nat) (ports rets : List Nat) (S0 SA SF : Trie) : Bool :=
  guard (Nat.ble 1 p.h) <|
  guard (wfK S0 p.d) <|
  guard (Nat.ble p.n (Nat.pow 2 p.d)) <|
  guard (Nat.ble (Nat.mul 2 v) p.n) <|
  p.tab.getK 0 fun c0 => guard (Nat.beq (Nat.land c0 255) 0) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) hm) fun Oh =>
  guard (Nat.beq (Nat.mul Oh hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1)) <|
  guard (portsK p hm Oh (Nat.add 8 p.h) v S0 SA SF ports 0) <|
  guard (slotsK p (Nat.mul 2 v) S0 SF (Nat.sub p.n (Nat.mul 2 v))) (retsK p SA rets)

end GLab
