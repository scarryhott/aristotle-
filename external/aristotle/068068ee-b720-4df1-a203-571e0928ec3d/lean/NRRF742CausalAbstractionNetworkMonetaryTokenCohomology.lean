import Mathlib

/-!
# NRRF742 — Causal Abstraction Networks: one monetary token from the global topology, and the
cohomology that constrains the gluing of local perspectives

Agents sit at the nodes of a network.  Each agent carries its own local perspective — its own
scale of value — and along every boundary between two interacting agents there is a declared
**transfer** `w i j`: what one unit of `i`'s local scale is worth in `j`'s.  This is exactly the
connection of a causal abstraction network: the translation between two subjective, context
dependent readings of the same world.  Nothing global is assumed — no shared dataset, no single
chart, only local data and the topology of who talks to whom.

The question addressed here is the one raised: *can a single monetary token be formed across the
whole interconnection, and what constrains the gluing?*  The answer proved below is that the
constraint is exactly a first cohomology class of the network with coefficients in the value
group, and that the constraint runs in both directions.

* **§1–§2 — the gluing theorem.**  For a connected network with antisymmetric local transfers,
  the following are one and the same (`glues_tfae`, `glues_iff_noArbitrage`): a **global token**
  exists (a single value scale `p` whose differences reproduce every declared transfer); value is
  **route independent**; and **no closed loop of transfers accumulates anything**.  The holonomy
  of loops is the whole obstruction.
* **The independent source.**  Two tokens can differ only by a constant (`token_diff_const`), so
  naming the value at one distinguished agent — one independent source of the money value —
  collapses the whole family of admissible local perspectives to exactly one global reading
  (`existsUnique_token_of_source`).  The superposition of perspectives is a torsor; the source is
  what collapses it; the constant it fixes is the hidden variable that no transaction can see
  (`dOf_eq_on_edges_iff_shift`).
* **§3 — the mutual constraint.**  Cohomology constrains the sheaf: a vanishing class is exactly
  what lets local sections glue.  And the sheaf constrains the cohomology: two systems of local
  data are related by a relabelling of local units exactly when they carry the same loop
  holonomies (`gauge_equivalent_iff_same_holonomy`), so the class is a complete invariant of the
  local data modulo the individual perspectives.
* **§4 — the connection Laplacian.**  The quadratic form `energy` of the connection Laplacian is
  a quantitative metric of misalignment: it is non-negative, blind to the global constant, zero
  exactly at a global token, and can be driven to zero exactly when the class vanishes
  (`exists_energy_zero_iff_noArbitrage`).
* **§5 — mixture causal models.**  When mechanisms shift with context, a context-independent
  token exists iff the contexts agree on every boundary and one of them glues (`mixtureGlues_iff`).
  Contextwise coherence is strictly weaker than joint coherence
  (`twoMix_contextwise_glues`, `twoMix_not_mixtureGlues`).
* **§6 — the monetary reading.**  In multiplicative form the same theorem says: a single price
  vector (a common numéraire, one token for the network) reproducing all local exchange rates
  exists iff every cycle of exchanges returns exactly what it started with — no arbitrage
  (`exists_numeraire_iff_cycle_products_one`).
* **§7 — models.**  A star network (a tree, a rigid hierarchy of transactions) is *always*
  unobstructed: every declaration whatsoever glues (`starNet_glues`).  The twisted triangle is
  obstructed: its loop carries holonomy `3`, and no unified token exists (`triW_not_glues`).  So
  topology, not the size of the numbers, decides whether one token can exist.

Nothing here asserts an economic theory; what is proved is the internal mathematics of the
network, its connection, and its first cohomology.
-/

namespace NRRF742

universe u v

variable {V : Type u} {G : Type v}

/-- A **causal agent network**: agents (vertices) with a symmetric "shares a boundary" relation. -/
structure Net (V : Type u) where
  /-- two agents interact -/
  adj : V → V → Prop
  /-- interaction is symmetric -/
  symm : ∀ {i j}, adj i j → adj j i

/-- The endpoint of the vertex list `u` read as a walk starting at `i`. -/
def term : V → List V → V
  | i, [] => i
  | _, j :: t => term j t

/-- `u` is a walk in `N` starting at `i`. -/
def Net.IsWalk (N : Net V) : V → List V → Prop
  | _, [] => True
  | i, j :: t => N.adj i j ∧ N.IsWalk j t

@[simp] theorem term_nil (i : V) : term i ([] : List V) = i := rfl
@[simp] theorem term_cons (i j : V) (t : List V) : term i (j :: t) = term j t := rfl

@[simp] theorem Net.isWalk_nil (N : Net V) (i : V) : N.IsWalk i [] := trivial

@[simp] theorem Net.isWalk_cons (N : Net V) (i j : V) (t : List V) :
    N.IsWalk i (j :: t) ↔ N.adj i j ∧ N.IsWalk j t := Iff.rfl

theorem term_append (i : V) (u v : List V) : term i (u ++ v) = term (term i u) v := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simpa using ih j

theorem Net.isWalk_append (N : Net V) (i : V) (u v : List V) :
    N.IsWalk i (u ++ v) ↔ N.IsWalk i u ∧ N.IsWalk (term i u) v := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp [Net.IsWalk, ih j, and_assoc]

/-- The network is **connected**: every agent is reachable from every agent. -/
def Net.Connected (N : Net V) : Prop := ∀ i j : V, ∃ u, N.IsWalk i u ∧ term i u = j

/-! ## §1  Local exchange data and its holonomy -/

section Cochain

variable [AddCommGroup G]

/-- A **transfer cochain**: `w i j` is the value agent `j` assigns to one unit of agent `i`'s
local scale, read additively (a log-rate).  This is the connection of the causal abstraction
network: the translation identifying `i`'s local perspective with `j`'s. -/
abbrev Cochain (V : Type u) (G : Type v) := V → V → G

/-- Antisymmetry: reading a transfer backwards negates it. -/
def Anti (w : Cochain V G) : Prop := ∀ i j, w j i = -w i j

/-- **Holonomy**: the total transfer accumulated along a walk. -/
def hol (w : Cochain V G) : V → List V → G
  | _, [] => 0
  | i, j :: t => w i j + hol w j t

@[simp] theorem hol_nil (w : Cochain V G) (i : V) : hol w i [] = 0 := rfl
@[simp] theorem hol_cons (w : Cochain V G) (i j : V) (t : List V) :
    hol w i (j :: t) = w i j + hol w j t := rfl

theorem hol_append (w : Cochain V G) (i : V) (u v : List V) :
    hol w i (u ++ v) = hol w i u + hol w (term i u) v := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp [ih j, add_assoc]

theorem hol_add (w₁ w₂ : Cochain V G) (i : V) (u : List V) :
    hol (fun a b => w₁ a b + w₂ a b) i u = hol w₁ i u + hol w₂ i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp [ih j]; abel

/-- The reversed walk: the vertex list of the walk `term i u → i`. -/
def revWalk : V → List V → List V
  | _, [] => []
  | i, j :: t => revWalk j t ++ [i]

@[simp] theorem revWalk_nil (i : V) : revWalk i ([] : List V) = [] := rfl

theorem term_revWalk (i : V) (u : List V) : term (term i u) (revWalk i u) = i := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp [revWalk, term_append, ih j]

theorem Net.isWalk_revWalk (N : Net V) (i : V) (u : List V) (h : N.IsWalk i u) :
    N.IsWalk (term i u) (revWalk i u) := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih =>
      obtain ⟨hij, ht⟩ := h
      simp only [revWalk, term_cons]
      rw [N.isWalk_append]
      refine ⟨ih j ht, ?_⟩
      rw [term_revWalk]
      exact ⟨N.symm hij, trivial⟩

theorem hol_revWalk (w : Cochain V G) (hw : Anti w) (i : V) (u : List V) :
    hol w (term i u) (revWalk i u) = -hol w i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih =>
      simp only [revWalk, term_cons]
      rw [hol_append, ih j, term_revWalk]
      simp [hw i j]

end Cochain

/-! ## §2  Global tokens, no-arbitrage, and path coherence -/

section Token

variable [AddCommGroup G] (N : Net V) (w : Cochain V G)

/-- A **global token**: one monetary scale `p` on the whole network whose differences are exactly
the declared local transfers.  This is a global section of the causal abstraction network. -/
def IsToken (p : V → G) : Prop := ∀ i j, N.adj i j → w i j = p j - p i

/-- The transfer cochain **glues**: some global token exists (the class is exact). -/
def Glues : Prop := ∃ p : V → G, IsToken N w p

/-- **No arbitrage**: every closed walk accumulates zero transfer. -/
def NoArbitrage : Prop := ∀ i u, N.IsWalk i u → term i u = i → hol w i u = 0

/-- **Path coherence**: the accumulated transfer between two agents does not depend on the route. -/
def PathCoherent : Prop :=
  ∀ i u v, N.IsWalk i u → N.IsWalk i v → term i u = term i v → hol w i u = hol w i v

variable {N w}

theorem hol_of_isToken {p : V → G} (hp : IsToken N w p) :
    ∀ i u, N.IsWalk i u → hol w i u = p (term i u) - p i := by
  intro i u
  induction u generalizing i with
  | nil => simp
  | cons j t ih =>
      rintro ⟨hij, ht⟩
      rw [hol_cons, ih j ht, hp i j hij, term_cons]
      abel

theorem pathCoherent_of_glues (h : Glues N w) : PathCoherent N w := by
  obtain ⟨p, hp⟩ := h
  intro i u v hu hv huv
  rw [hol_of_isToken hp i u hu, hol_of_isToken hp i v hv, huv]

theorem noArbitrage_of_glues (h : Glues N w) : NoArbitrage N w := by
  obtain ⟨p, hp⟩ := h
  intro i u hu hui
  rw [hol_of_isToken hp i u hu, hui, sub_self]

theorem pathCoherent_of_noArbitrage (hw : Anti w) (h : NoArbitrage N w) : PathCoherent N w := by
  intro i u v hu hv huv
  have hclosed : hol w i (u ++ revWalk i v) = 0 := by
    refine h i _ ?_ ?_
    · rw [N.isWalk_append]
      exact ⟨hu, by rw [huv]; exact N.isWalk_revWalk i v hv⟩
    · rw [term_append, huv, term_revWalk]
  rw [hol_append, huv, hol_revWalk w hw] at hclosed
  have hsub : hol w i u - hol w i v = 0 := by rw [sub_eq_add_neg]; exact hclosed
  exact sub_eq_zero.mp hsub

theorem glues_of_pathCoherent [Nonempty V] (hc : N.Connected) (h : PathCoherent N w) :
    Glues N w := by
  classical
  set s : V := Classical.arbitrary V with hs
  choose walk hwalk hterm using hc s
  refine ⟨fun i => hol w s (walk i), ?_⟩
  intro i j hij
  have hw' : N.IsWalk s (walk i ++ [j]) := by
    rw [N.isWalk_append]
    exact ⟨hwalk i, by rw [hterm i]; exact ⟨hij, trivial⟩⟩
  have hterm' : term s (walk i ++ [j]) = term s (walk j) := by
    rw [term_append, hterm i, hterm j]; rfl
  have := h s (walk i ++ [j]) (walk j) hw' (hwalk j) hterm'
  rw [hol_append, hterm i] at this
  simp only [hol_cons, hol_nil, add_zero] at this
  show w i j = hol w s (walk j) - hol w s (walk i)
  rw [← this]
  abel

/-! ### The main gluing theorem -/

/-- **One unified token exists iff there is no arbitrage.**  On a connected network of agents,
the local transfer data of the causal abstraction network glue to a single global monetary scale
exactly when every closed loop of transfers accumulates nothing. -/
theorem glues_iff_noArbitrage [Nonempty V] (hc : N.Connected) (hw : Anti w) :
    Glues N w ↔ NoArbitrage N w :=
  ⟨noArbitrage_of_glues, fun h => glues_of_pathCoherent hc (pathCoherent_of_noArbitrage hw h)⟩

/-- The three readings of alignment coincide: a global token, route independence of value, and
absence of arbitrage loops. -/
theorem glues_tfae [Nonempty V] (hc : N.Connected) (hw : Anti w) :
    [Glues N w, PathCoherent N w, NoArbitrage N w].TFAE := by
  tfae_have 1 → 2 := pathCoherent_of_glues
  tfae_have 2 → 1 := glues_of_pathCoherent hc
  tfae_have 1 → 3 := noArbitrage_of_glues
  tfae_have 3 → 2 := pathCoherent_of_noArbitrage hw
  tfae_finish

/-! ### The token is unique once one independent source of value is fixed -/

/-- Two global tokens for the same transfer data differ by a constant: the absolute level of value
is a hidden variable, invisible to every transaction. -/
theorem token_diff_const (hc : N.Connected) {p q : V → G} (hp : IsToken N w p)
    (hq : IsToken N w q) (i j : V) : p j - q j = p i - q i := by
  obtain ⟨u, hu, hterm⟩ := hc i j
  have h1 := hol_of_isToken hp i u hu
  have h2 := hol_of_isToken hq i u hu
  rw [hterm] at h1 h2
  have h : p j - p i = q j - q i := by rw [← h1, h2]
  exact sub_eq_sub_iff_sub_eq_sub.mp h

/-- Fixing the value at one distinguished agent — one independent source of the money value —
pins the token exactly. -/
theorem token_unique_of_source (hc : N.Connected) {p q : V → G} (hp : IsToken N w p)
    (hq : IsToken N w q) (s : V) (hs : p s = q s) : p = q := by
  funext i
  have := token_diff_const hc hp hq s i
  rw [hs, sub_self] at this
  exact sub_eq_zero.mp this

/-- Translating a token by a constant is again a token: the gauge freedom of value. -/
theorem isToken_add_const {p : V → G} (hp : IsToken N w p) (g : G) :
    IsToken N w (fun i => p i + g) := by
  intro i j hij
  simp only
  rw [hp i j hij]
  abel

/-- **Collapse of the superposition.**  On a connected, arbitrage-free network, and for each
prescribed value `g` at the source `s`, there is exactly one global token.  The family of local
perspectives (a `G`-torsor: the superposition) collapses to a single monetary reading precisely
when one independent source of value is named. -/
theorem existsUnique_token_of_source [Nonempty V] (hc : N.Connected) (hw : Anti w)
    (hna : NoArbitrage N w) (s : V) (g : G) : ∃! p : V → G, IsToken N w p ∧ p s = g := by
  obtain ⟨p₀, hp₀⟩ := (glues_iff_noArbitrage hc hw).mpr hna
  refine ⟨fun i => p₀ i + (g - p₀ s), ⟨isToken_add_const hp₀ _, by simp⟩, ?_⟩
  rintro q ⟨hq, hqs⟩
  have hs : q s = p₀ s + (g - p₀ s) := by rw [hqs]; abel
  exact token_unique_of_source hc hq (isToken_add_const hp₀ _) s hs

end Token

/-! ## §3  The cohomology class is a complete invariant of the local data -/

section Cohomology

variable [AddCommGroup G] {N : Net V} {w₁ w₂ : Cochain V G}

/-- The coboundary of a value assignment: the transfers it induces. -/
def dOf (p : V → G) : Cochain V G := fun i j => p j - p i

theorem anti_dOf (p : V → G) : Anti (dOf p) := by
  intro i j; simp only [dOf]; abel

@[simp] theorem dOf_add_const (p : V → G) (g : G) : dOf (fun i => p i + g) = dOf p := by
  funext i j; simp only [dOf]; abel

theorem isToken_dOf (M : Net V) (p : V → G) : IsToken M (dOf p) p := fun _ _ _ => rfl

/-- Coboundaries have no holonomy: an exact transfer system never produces arbitrage. -/
theorem hol_dOf_closed (p : V → G) (i : V) (u : List V) (hu : N.IsWalk i u)
    (hi : term i u = i) : hol (dOf p) i u = 0 :=
  noArbitrage_of_glues ⟨p, isToken_dOf N p⟩ i u hu hi

/-- **Value is a hidden variable of money.**  On a connected network two value assignments induce
the same transfers across every boundary exactly when they differ by one global constant: the
absolute level is never visible in any transaction, only differences are. -/
theorem dOf_eq_on_edges_iff_shift [Nonempty V] (hc : N.Connected) (p q : V → G) :
    (∀ i j, N.adj i j → dOf p i j = dOf q i j) ↔ ∃ g : G, ∀ i, q i = p i + g := by
  constructor
  · intro h
    have hp : IsToken N (dOf p) p := isToken_dOf N p
    have hq : IsToken N (dOf p) q := fun i j hij => (h i j hij).trans rfl
    obtain ⟨s⟩ := ‹Nonempty V›
    refine ⟨q s - p s, fun i => ?_⟩
    have := token_diff_const hc hp hq s i
    have h2 : p i - q i = p s - q s := this
    have : q i = p i - (p s - q s) := by
      rw [← h2]; abel
    rw [this]; abel
  · rintro ⟨g, hg⟩ i j _
    simp only [dOf, hg]
    abel

theorem hol_sub (w₁ w₂ : Cochain V G) (i : V) (u : List V) :
    hol (fun a b => w₁ a b - w₂ a b) i u = hol w₁ i u - hol w₂ i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp only [hol_cons, ih j]; abel

theorem anti_sub (h₁ : Anti w₁) (h₂ : Anti w₂) : Anti (fun a b => w₁ a b - w₂ a b) := by
  intro i j; simp only [h₁ i j, h₂ i j]; abel

/-- **Cohomology constrains the sheaf, and the sheaf constrains the cohomology.**  On a connected
network, two systems of local transfer data are related by a relabelling of local units (a gauge
transformation of the perspectives) exactly when they assign the same holonomy to every loop —
exactly when they have the same cohomology class. -/
theorem gauge_equivalent_iff_same_holonomy [Nonempty V] (hc : N.Connected) (h₁ : Anti w₁)
    (h₂ : Anti w₂) :
    (∃ p : V → G, ∀ i j, N.adj i j → w₁ i j - w₂ i j = p j - p i) ↔
      ∀ i u, N.IsWalk i u → term i u = i → hol w₁ i u = hol w₂ i u := by
  have key := glues_iff_noArbitrage (w := fun a b => w₁ a b - w₂ a b) hc (anti_sub h₁ h₂)
  constructor
  · rintro ⟨p, hp⟩ i u hu hi
    have hz := noArbitrage_of_glues (w := fun a b => w₁ a b - w₂ a b) ⟨p, hp⟩ i u hu hi
    rw [hol_sub] at hz
    exact sub_eq_zero.mp hz
  · intro h
    obtain ⟨p, hp⟩ := key.mpr (by
      intro i u hu hi
      rw [hol_sub, h i u hu hi, sub_self])
    exact ⟨p, hp⟩

end Cohomology

/-! ## §4  The connection Laplacian: alignment as vanishing energy -/

section Laplacian

open Finset

variable [Fintype V] (N : Net V) (w : Cochain V ℝ)

open Classical in
/-- The **connection energy** (the quadratic form of the connection Laplacian of the network):
the total squared disagreement between a candidate global token and the declared local
transfers. -/
noncomputable def energy (p : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V, if N.adj i j then (p j - p i - w i j) ^ 2 else 0

theorem energy_nonneg (p : V → ℝ) : 0 ≤ energy N w p := by
  classical
  refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
  by_cases h : N.adj i j <;> simp [h, sq_nonneg]

/-- The energy vanishes exactly at a global token. -/
theorem energy_eq_zero_iff (p : V → ℝ) : energy N w p = 0 ↔ IsToken N w p := by
  classical
  rw [energy]
  constructor
  · intro h i j hij
    have h1 : ∀ a ∈ (univ : Finset V),
        (0:ℝ) ≤ ∑ b : V, if N.adj a b then (p b - p a - w a b) ^ 2 else 0 := by
      intro a _
      refine sum_nonneg fun b _ => ?_
      by_cases hb : N.adj a b <;> simp [hb, sq_nonneg]
    have h2 := (sum_eq_zero_iff_of_nonneg h1).mp h i (mem_univ i)
    have h3 : ∀ b ∈ (univ : Finset V),
        (0:ℝ) ≤ if N.adj i b then (p b - p i - w i b) ^ 2 else 0 := by
      intro b _
      by_cases hb : N.adj i b <;> simp [hb, sq_nonneg]
    have h4 := (sum_eq_zero_iff_of_nonneg h3).mp h2 j (mem_univ j)
    rw [if_pos hij] at h4
    have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
    linarith
  · intro hp
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
    by_cases hb : N.adj i j
    · rw [if_pos hb, hp i j hb, sub_self]
      norm_num
    · rw [if_neg hb]

/-- The energy does not see the absolute level of value. -/
theorem energy_add_const (p : V → ℝ) (g : ℝ) : energy N w (fun i => p i + g) = energy N w p := by
  classical
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hb : N.adj i j
  · simp only [if_pos hb]
    ring_nf
  · simp [hb]

/-- **The Laplacian metric detects the cohomological obstruction.**  On a connected network the
connection energy can be driven to zero exactly when there is no arbitrage loop. -/
theorem exists_energy_zero_iff_noArbitrage [Nonempty V] (hc : N.Connected) (hw : Anti w) :
    (∃ p, energy N w p = 0) ↔ NoArbitrage N w := by
  rw [← glues_iff_noArbitrage hc hw]
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p, (energy_eq_zero_iff N w p).mp hp⟩
  · rintro ⟨p, hp⟩; exact ⟨p, (energy_eq_zero_iff N w p).mpr hp⟩

end Laplacian

/-! ## §5  Mixture causal models: one token across shifting contexts -/

section Mixture

variable [AddCommGroup G] {C : Type*} {N : Net V} {W : C → Cochain V G}

/-- A **mixture** of local causal mechanisms glues if one single token reads all contexts. -/
def MixtureGlues (N : Net V) (W : C → Cochain V G) : Prop := ∃ p : V → G, ∀ c, IsToken N (W c) p

/-- **A context-independent token exists iff the contexts agree on every boundary and one of them
glues.**  Mechanism shift across contexts is an obstruction of its own, over and above the
per-context cohomology. -/
theorem mixtureGlues_iff [Nonempty C] :
    MixtureGlues N W ↔
      ((∀ c c' i j, N.adj i j → W c i j = W c' i j) ∧ ∀ c, Glues N (W c)) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨fun c c' i j hij => by rw [hp c i j hij, hp c' i j hij], fun c => ⟨p, hp c⟩⟩
  · rintro ⟨hagree, hglue⟩
    obtain ⟨p, hp⟩ := hglue (Classical.arbitrary C)
    exact ⟨p, fun c i j hij => by rw [hagree c (Classical.arbitrary C) i j hij]; exact hp i j hij⟩

/-- Each context gluing separately is not enough. -/
theorem mixture_contextwise_not_enough
    (hne : ∃ c c' i j, N.adj i j ∧ W c i j ≠ W c' i j) : ¬ MixtureGlues N W := by
  rintro ⟨p, hp⟩
  obtain ⟨c, c', i, j, hij, hne⟩ := hne
  exact hne (by rw [hp c i j hij, hp c' i j hij])

end Mixture

/-! ## §6  The multiplicative reading: exchange rates and a common numéraire -/

section Rates

variable {N : Net V} {r : V → V → ℝ}

/-- The additive (log) transfer cochain of a system of positive exchange rates. -/
noncomputable def logCochain (r : V → V → ℝ) : Cochain V ℝ := fun i j => Real.log (r i j)

theorem anti_logCochain (hpos : ∀ i j, 0 < r i j) (hinv : ∀ i j, r i j * r j i = 1) :
    Anti (logCochain r) := by
  intro i j
  have hij : r i j ≠ 0 := ne_of_gt (hpos i j)
  have hinv' : r j i = (r i j)⁻¹ := by
    field_simp
    linarith [hinv i j]
  simp [logCochain, hinv', Real.log_inv]

/-- The product of the exchange rates along a walk. -/
def prodAlong (r : V → V → ℝ) : V → List V → ℝ
  | _, [] => 1
  | i, j :: t => r i j * prodAlong r j t

theorem prodAlong_eq_exp_hol (hpos : ∀ i j, 0 < r i j) (i : V) (u : List V) :
    prodAlong r i u = Real.exp (hol (logCochain r) i u) := by
  induction u generalizing i with
  | nil => simp [prodAlong]
  | cons j t ih =>
      simp only [prodAlong, hol_cons, Real.exp_add, ih j, logCochain,
        Real.exp_log (hpos i j)]

/-- **No arbitrage in the multiplicative form is exactly the existence of one common numéraire.**
A single price vector `π` — one unified token for the whole network — reproduces all the local
exchange rates iff every cycle of exchanges returns exactly what it started with. -/
theorem exists_numeraire_iff_cycle_products_one [Nonempty V] (hc : N.Connected)
    (hpos : ∀ i j, 0 < r i j) (hinv : ∀ i j, r i j * r j i = 1) :
    (∃ π : V → ℝ, (∀ i, 0 < π i) ∧ ∀ i j, N.adj i j → r i j = π j / π i) ↔
      ∀ i u, N.IsWalk i u → term i u = i → prodAlong r i u = 1 := by
  constructor
  · rintro ⟨π, hπpos, hπ⟩ i u hu hi
    have hglue : Glues N (logCochain r) := by
      refine ⟨fun a => Real.log (π a), fun a b hab => ?_⟩
      rw [logCochain, hπ a b hab, Real.log_div (ne_of_gt (hπpos b)) (ne_of_gt (hπpos a))]
    rw [prodAlong_eq_exp_hol hpos, noArbitrage_of_glues hglue i u hu hi, Real.exp_zero]
  · intro h
    have hna : NoArbitrage N (logCochain r) := by
      intro i u hu hi
      have := h i u hu hi
      rw [prodAlong_eq_exp_hol hpos] at this
      exact (Real.exp_eq_one_iff _).mp this
    obtain ⟨p, hp⟩ := (glues_iff_noArbitrage hc (anti_logCochain hpos hinv)).mpr hna
    refine ⟨fun a => Real.exp (p a), fun a => Real.exp_pos _, fun a b hab => ?_⟩
    have := hp a b hab
    rw [logCochain] at this
    rw [← Real.exp_log (hpos a b), this, Real.exp_sub]

end Rates

/-! ## §7  Models: a tree always glues, a cycle need not -/

section Models

/-- The star network on `V` with hub `hub`: every agent talks to the hub only. -/
def starNet {V : Type u} (hub : V) : Net V where
  adj i j := i ≠ j ∧ (i = hub ∨ j = hub)
  symm := by
    rintro i j ⟨hne, h⟩
    exact ⟨hne.symm, h.symm⟩

theorem starNet_connected {V : Type u} (hub : V) : (starNet hub).Connected := by
  intro i j
  by_cases hij : i = j
  · exact ⟨[], trivial, by simp [hij]⟩
  by_cases hi : i = hub
  · exact ⟨[j], ⟨⟨hij, Or.inl hi⟩, trivial⟩, rfl⟩
  by_cases hj : j = hub
  · exact ⟨[j], ⟨⟨hij, Or.inr hj⟩, trivial⟩, rfl⟩
  exact ⟨[hub, j], ⟨⟨hi, Or.inr rfl⟩, ⟨fun h => hj h.symm, Or.inl rfl⟩, trivial⟩, rfl⟩

/-- **A tree has no obstruction**: on a star network every antisymmetric system of local
transfers glues into a unified token, whatever the agents declare. -/
theorem starNet_glues {V : Type u} (hub : V) (w : Cochain V ℝ) (hw : Anti w) :
    Glues (starNet hub) w := by
  refine ⟨fun i => w hub i, ?_⟩
  have hself : w hub hub = 0 := by have := hw hub hub; linarith
  rintro i j ⟨hne, hi | hj⟩
  · rw [hi]
    show w hub j = w hub j - w hub hub
    rw [hself]; ring
  · rw [hj]
    show w i hub = w hub hub - w hub i
    rw [hself, hw hub i]; ring

/-- The triangle of three agents, all pairs interacting. -/
def triNet : Net (Fin 3) where
  adj i j := i ≠ j
  symm := fun h => h.symm

theorem triNet_connected : triNet.Connected := by
  intro i j
  by_cases hij : i = j
  · exact ⟨[], trivial, by simp [hij]⟩
  · exact ⟨[j], ⟨hij, trivial⟩, rfl⟩

/-- A cyclically twisted system of local transfers on the triangle. -/
def triW : Cochain (Fin 3) ℝ := fun i j =>
  match (i : ℕ), (j : ℕ) with
  | 0, 1 => 1
  | 1, 2 => 1
  | 2, 0 => 1
  | 1, 0 => -1
  | 2, 1 => -1
  | 0, 2 => -1
  | _, _ => 0

theorem triW_anti : Anti triW := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [triW]

/-- The loop `0 → 1 → 2 → 0` accumulates a strictly positive transfer: an arbitrage cycle. -/
theorem triW_loop_holonomy : hol triW 0 [1, 2, 0] = 3 := by
  norm_num [triW]

/-- **A cycle can be obstructed**: no unified token exists for the twisted triangle. -/
theorem triW_not_glues : ¬ Glues triNet triW := by
  rintro ⟨p, hp⟩
  have h01 := hp 0 1 (show (0 : Fin 3) ≠ 1 by decide)
  have h12 := hp 1 2 (show (1 : Fin 3) ≠ 2 by decide)
  have h20 := hp 2 0 (show (2 : Fin 3) ≠ 0 by decide)
  norm_num [triW] at h01 h12 h20
  linarith

theorem triW_arbitrage : ¬ NoArbitrage triNet triW := by
  intro h
  have hw : triNet.IsWalk 0 [1, 2, 0] :=
    ⟨show (0 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, trivial⟩
  have := h 0 [1, 2, 0] hw rfl
  rw [triW_loop_holonomy] at this
  norm_num at this

/-- Two contexts on a two-agent network, each internally coherent, disagreeing on the boundary. -/
def twoNet : Net (Fin 2) where
  adj i j := i ≠ j
  symm := fun h => h.symm

noncomputable def twoMix : Bool → Cochain (Fin 2) ℝ :=
  fun c => dOf (fun i => if c then (i : ℝ) else 2 * (i : ℝ))

/-- Each context glues on its own … -/
theorem twoMix_contextwise_glues (c : Bool) : Glues twoNet (twoMix c) :=
  ⟨_, isToken_dOf twoNet _⟩

/-- … yet no single token reads both contexts: mechanism shift is its own obstruction. -/
theorem twoMix_not_mixtureGlues : ¬ MixtureGlues twoNet twoMix := by
  refine mixture_contextwise_not_enough ⟨true, false, 0, 1, show (0 : Fin 2) ≠ 1 by decide, ?_⟩
  norm_num [twoMix, dOf]

end Models

/-! ## §8  The answer, in one statement -/

/-- **NRRF742, collected.**  For a connected network of agents carrying antisymmetric local
transfer data:

1. a single unified token exists iff no loop of transfers accumulates anything (the cohomology
   class is the whole obstruction);
2. naming one independent source of value collapses the family of admissible tokens to exactly
   one, and any two tokens differ only by that hidden constant;
3. the connection Laplacian's energy can be driven to zero exactly in the unobstructed case;
4. two systems of local data are gauge equivalent iff they carry the same loop holonomies — the
   class constrains the gluing and the gluing determines the class;
5. in the mixture (context-dependent) setting a context-independent token exists iff the contexts
   agree on every boundary and one of them glues;
6. a star network is always unobstructed, while the twisted triangle is not. -/
theorem nrrf742_answer {V : Type u} [Nonempty V] [Fintype V] (N : Net V) (w : Cochain V ℝ)
    (hc : N.Connected) (hw : Anti w) (s : V) :
    (Glues N w ↔ NoArbitrage N w) ∧
    ((∃ p, energy N w p = 0) ↔ NoArbitrage N w) ∧
    (∀ p q : V → ℝ, IsToken N w p → IsToken N w q → p s = q s → p = q) ∧
    (NoArbitrage N w → ∀ g : ℝ, ∃! p : V → ℝ, IsToken N w p ∧ p s = g) :=
  ⟨glues_iff_noArbitrage hc hw, exists_energy_zero_iff_noArbitrage N w hc hw,
    fun _ _ hp hq h => token_unique_of_source hc hp hq s h,
    fun h g => existsUnique_token_of_source hc hw h s g⟩

end NRRF742
