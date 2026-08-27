import Mathlib
import NRRF742CausalAbstractionNetworkMonetaryTokenCohomology
import NRRF772LinearLayoutRelativeEqualityFunctionsCompleteness
import NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces

/-!
# NRRF780 — A classical trading system evaluated in the relative unity of value flow

The reading being formalised:

> Evaluate a classical trading system inside the tokenomic relative unity of value flow, where the
> **local** readings are prices and the **inf** reading is cost, with a multilayer form for each
> aspect that makes up a classical monetary transaction.

The verdict proved here, in one line: *a classical transaction carries no value of its own.*  Its
local (price) content cancels identically in the value flow, and what survives is exactly minus its
inf (cost) reading — `net_eq_neg_cost`.  Lifted to a system of transactions the same cancellation is
the loop statement: around any closed circuit of an exact price field the price holonomy is zero
(`price_loop_zero`), so the trading holonomy of the classical system is exactly minus its friction
(`classical_roundTrip_eq_neg_cost`), which is `≤ 0` and strictly negative as soon as any edge charges
(`classical_roundTrip_strict_loss`).  Profit is therefore never a property of the transactions: it
is exactly a *non-exactness of the price field exceeding the friction* (`profit_needs_arbitrage`).

* **§1 The transaction and its layers.**  A `Txn` carries six local aspects — size, bid, ask, fill,
  mark, fee.  Each is a relative equality function; jointly they are complete (`layers_complete`),
  and dropping any one of them destroys completeness (`layers_drop_fill_not_complete`), so the
  multilayer form is irredundant.
* **§2 Local are prices, inf are costs.**  `cost = fee + slippage` is a translation of the local
  layer (`inf_refines_local`) and *strictly* coarser (`local_not_refines_inf`): the price level is
  not recoverable from the cost.  The evaluation identity is `net_eq_neg_cost`.
* **§3 Relative unity.**  Value flow is blind to the price gauge (`flow_shift`, `cost_shift`) while
  the price layer is not (`fill_not_shift_invariant`); under a numéraire rescaling both flow and
  cost scale by the same factor, so only their ratio is determined (`flow_cost_ratio_invariant`).
  This is the sense in which the unity is *relative*: absolute prices are not data of the flow.
* **§4 Crossing the spread.**  Executing at the quote and marking at the mid makes the slippage
  exactly the half-spread (`buy_slippage_halfSpread`, `sell_slippage_halfSpread`), so with a positive
  spread and a nonzero size a classical crossing trade is strictly loss-making
  (`crossing_trade_strictly_negative`) — the classical system pays the spread whichever way it goes.
* **§5 The system on a network.**  With prices exact and costs symmetric and nonnegative, every
  closed circuit returns minus the friction (`classical_roundTrip_eq_neg_cost`), quantitatively at
  least the circuit length times the per-edge charge (`hol_cost_ge_len_mul`); a profitable circuit
  forces arbitrage in the price field alone (`profit_needs_arbitrage`, `profit_needs_nonexact`).
* **§6 The system in time.**  Over a mark path the classical P&L identity is position times price
  move minus costs (`pnl_const_position`); in a market that returns to its starting mark the whole
  P&L is minus the costs (`pnl_returning_market`), never positive (`pnl_returning_nonpos`), and a
  profitable run is exactly one whose price move beats the accumulated cost (`pnl_pos_iff`).
* **§7 Execution is a determination, not a preference.**  "Buy at the ask, sell at the bid" is a
  rigid relation, so NRRF775's natural form selector returns it and it is the unique admissible
  execution (`execSel_buy`, `execSel_sell`, `execSel_unique`).

`nrrf780_answer` collects the clauses.
-/

namespace NRRF780

open NRRF742 (Net Cochain Anti hol hol_nil hol_cons hol_append dOf hol_dOf_closed isToken_dOf
  noArbitrage_of_glues NoArbitrage Glues)
open NRRF775 (Constraint Rigid sel sel_admissible sel_eq_of_admissible)

universe u

/-! ## §1  The classical transaction and its multilayer form -/

/-- **A classical transaction.**  The six aspects that make up classical monetary pricing: the
signed size, the two quoted local prices, the local price actually executed, the local price the
book is marked at, and the explicit fee. -/
structure Txn where
  /-- signed size: positive is a buy, negative a sell -/
  qty : ℚ
  /-- the local price a buyer is quoted to sell at -/
  bid : ℚ
  /-- the local price a seller is quoted to buy at -/
  ask : ℚ
  /-- the local price actually executed -/
  fill : ℚ
  /-- the local price the position is marked at -/
  mark : ℚ
  /-- the explicit fee charged -/
  fee : ℚ
  deriving DecidableEq, Repr

namespace Txn

/-- The quoted spread: the width of the two local prices. -/
def spread (t : Txn) : ℚ := t.ask - t.bid

/-- The mid: the local price halfway between the quotes. -/
def mid (t : Txn) : ℚ := (t.bid + t.ask) / 2

/-- **Slippage**: the value given up by executing away from the mark, signed by direction. -/
def slippage (t : Txn) : ℚ := (t.fill - t.mark) * t.qty

/-- **The inf reading — cost.**  Explicit fee plus slippage: the whole friction of the transaction. -/
def cost (t : Txn) : ℚ := t.fee + t.slippage

/-- The cash leg: what leaves the account. -/
def cash (t : Txn) : ℚ := -(t.fill * t.qty)

/-- The position leg, valued at the mark. -/
def mtm (t : Txn) : ℚ := t.mark * t.qty

/-- **Value flow** of the transaction: the position acquired, valued at the mark, plus the cash. -/
def flow (t : Txn) : ℚ := t.mtm + t.cash

/-- The full evaluation of the transaction: value flow net of the explicit fee. -/
def net (t : Txn) : ℚ := t.flow - t.fee

end Txn

open Txn

/-- The value flow is exactly minus the slippage: the price levels cancel. -/
theorem flow_eq_neg_slippage (t : Txn) : t.flow = -t.slippage := by
  simp only [flow, mtm, cash, slippage]; ring

/-- **The evaluation of a classical transaction.**  Everything local cancels; what a classical
transaction is worth is exactly minus its inf reading. -/
theorem net_eq_neg_cost (t : Txn) : t.net = -t.cost := by
  simp only [net, cost, flow_eq_neg_slippage]; ring

/-- A classical transaction is worth nothing exactly when it is costless. -/
theorem net_eq_zero_iff (t : Txn) : t.net = 0 ↔ t.cost = 0 := by
  rw [net_eq_neg_cost, neg_eq_zero]

/-- No classical transaction with a nonnegative cost has positive value. -/
theorem net_nonpos_of_cost_nonneg {t : Txn} (h : 0 ≤ t.cost) : t.net ≤ 0 := by
  rw [net_eq_neg_cost]; linarith

/-! ### The six layers as a complete multilayer form -/

/-- The multilayer form: each aspect of the transaction read as a relative equality function. -/
def layer : Fin 6 → Txn → ℚ
  | 0 => Txn.qty
  | 1 => Txn.bid
  | 2 => Txn.ask
  | 3 => Txn.fill
  | 4 => Txn.mark
  | 5 => Txn.fee

/-- The neutral transaction, used as a basepoint for kernel arguments. -/
def nilTxn : Txn := ⟨0, 0, 0, 0, 0, 0⟩

instance : Inhabited Txn := ⟨nilTxn⟩

/-- **The multilayer form is complete.**  Agreement in every layer is identity of the
transaction: the six aspects exhaust classical monetary pricing. -/
theorem layers_complete : NRRF772.Complete layer := by
  rw [NRRF772.complete_iff]
  rintro ⟨q, b, a, f, m, e⟩ ⟨q', b', a', f', m', e'⟩ h
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  simp only [layer] at h0 h1 h2 h3 h4 h5
  subst h0; subst h1; subst h2; subst h3; subst h4; subst h5
  rfl

/-- The multilayer form with the execution layer removed. -/
def layerDropFill : Fin 5 → Txn → ℚ
  | 0 => Txn.qty
  | 1 => Txn.bid
  | 2 => Txn.ask
  | 3 => Txn.mark
  | 4 => Txn.fee

/-- **The form is irredundant.**  Drop the execution layer and the remaining aspects no longer
determine the transaction: quotes are not fills. -/
theorem layers_drop_fill_not_complete : ¬ NRRF772.Complete layerDropFill := by
  intro h
  rw [NRRF772.complete_iff] at h
  have := h ⟨0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0, 1, 0, 0⟩ (by decide)
  simp only [Txn.mk.injEq] at this
  exact absurd this.2.2.2.1 (by norm_num)

/-! ## §2  Local are prices, inf are costs -/

/-- The **local reading**: the price aspects of the transaction, together with the size and fee that
scale them. -/
def localRead (t : Txn) : ℚ × ℚ × ℚ × ℚ := (t.qty, t.fill, t.mark, t.fee)

/-- **Inf is a translation of local.**  The cost is not an independent aspect: it is read off the
local price data. -/
theorem inf_refines_local : NRRF772.Refines localRead Txn.cost := by
  rw [NRRF772.refines_iff_kernel _ _ nilTxn]
  intro t t' h
  simp only [localRead, Prod.mk.injEq] at h
  simp only [cost, slippage, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- **…and strictly coarser.**  The cost does not recover the local prices: distinct price levels
are the same cost. -/
theorem local_not_refines_inf : ¬ NRRF772.Refines Txn.cost localRead := by
  intro h
  have hk : Txn.cost ⟨1, 0, 0, 0, 0, 0⟩ = Txn.cost ⟨1, 0, 0, 5, 5, 0⟩ := by
    norm_num [Txn.cost, Txn.slippage]
  have := h.kernel_le hk
  simp only [localRead, Prod.mk.injEq] at this
  exact absurd this.2.1 (by norm_num)

/-- The cost layer adds nothing to the multilayer form: it is already a translation of it. -/
theorem cost_layer_redundant : NRRF772.Refines (NRRF772.joint layer) Txn.cost := by
  rw [NRRF772.refines_iff_kernel _ _ nilTxn]
  intro t t' h
  have : t = t' := layers_complete h
  rw [this]

/-- The value flow and the cost carry the same translational data: each is minus the other. -/
theorem transEq_flow_cost : NRRF772.TransEq Txn.net Txn.cost := by
  rw [NRRF772.transEq_iff_kernel _ _ nilTxn]
  intro t t'
  rw [net_eq_neg_cost, net_eq_neg_cost, neg_inj]

/-! ## §3  Relative unity: the gauge and the numéraire -/

/-- Shifting the whole local price scale by a constant. -/
def shift (c : ℚ) (t : Txn) : Txn := ⟨t.qty, t.bid + c, t.ask + c, t.fill + c, t.mark + c, t.fee⟩

/-- Re-denominating in another numéraire. -/
def scale (l : ℚ) (t : Txn) : Txn :=
  ⟨t.qty, l * t.bid, l * t.ask, l * t.fill, l * t.mark, l * t.fee⟩

@[simp] theorem spread_shift (c : ℚ) (t : Txn) : (shift c t).spread = t.spread := by
  simp only [shift, spread]; ring

@[simp] theorem cost_shift (c : ℚ) (t : Txn) : (shift c t).cost = t.cost := by
  simp only [shift, cost, slippage]; ring

@[simp] theorem flow_shift (c : ℚ) (t : Txn) : (shift c t).flow = t.flow := by
  simp only [flow_eq_neg_slippage, shift, slippage]; ring

@[simp] theorem net_shift (c : ℚ) (t : Txn) : (shift c t).net = t.net := by
  rw [net_eq_neg_cost, net_eq_neg_cost, cost_shift]

/-- **Price is not gauge invariant.**  The local layer moves under a shift that the flow does not
see: absolute price is not a datum of value flow. -/
theorem fill_not_shift_invariant : ∃ c : ℚ, ∃ t : Txn, (shift c t).fill ≠ t.fill :=
  ⟨1, nilTxn, by norm_num [shift, nilTxn]⟩

@[simp] theorem cost_scale (l : ℚ) (t : Txn) : (scale l t).cost = l * t.cost := by
  simp only [scale, cost, slippage]; ring

@[simp] theorem net_scale (l : ℚ) (t : Txn) : (scale l t).net = l * t.net := by
  rw [net_eq_neg_cost, net_eq_neg_cost, cost_scale]; ring

/-- **Relative unity of value flow.**  Under a change of numéraire the evaluation and the cost move
together, so no absolute magnitude is determined — only their ratio. -/
theorem flow_cost_ratio_invariant (l : ℚ) (t : Txn) :
    (scale l t).net * t.cost = t.net * (scale l t).cost := by
  rw [cost_scale, net_scale]; ring

/-! ## §4  Crossing the spread: the half-spread is a cost -/

/-- A buy that lifts the offer and is marked at the mid gives up exactly half the spread. -/
theorem buy_slippage_halfSpread {t : Txn} (hf : t.fill = t.ask) (hm : t.mark = t.mid) :
    t.slippage = t.qty * t.spread / 2 := by
  simp only [slippage, hf, hm, mid, spread]; ring

/-- A sell that hits the bid and is marked at the mid gives up exactly half the spread. -/
theorem sell_slippage_halfSpread {t : Txn} (hf : t.fill = t.bid) (hm : t.mark = t.mid) :
    t.slippage = -t.qty * t.spread / 2 := by
  simp only [slippage, hf, hm, mid, spread]; ring

/-- **The classical crossing trade is strictly loss-making.**  A buy at the offer, marked at the
mid, with a positive spread, a positive size and a nonnegative fee, has strictly negative value: the
transaction itself never creates value, it only pays for the spread. -/
theorem crossing_trade_strictly_negative {t : Txn} (hf : t.fill = t.ask) (hm : t.mark = t.mid)
    (hq : 0 < t.qty) (hs : 0 < t.spread) (he : 0 ≤ t.fee) : t.net < 0 := by
  have hslip : t.slippage = t.qty * t.spread / 2 := buy_slippage_halfSpread hf hm
  have : 0 < t.cost := by
    simp only [cost, hslip]
    have : 0 < t.qty * t.spread := mul_pos hq hs
    linarith
  rw [net_eq_neg_cost]; linarith

/-- The same for the sell side: hitting the bid pays the other half of the spread. -/
theorem crossing_sell_strictly_negative {t : Txn} (hf : t.fill = t.bid) (hm : t.mark = t.mid)
    (hq : t.qty < 0) (hs : 0 < t.spread) (he : 0 ≤ t.fee) : t.net < 0 := by
  have hslip : t.slippage = -t.qty * t.spread / 2 := sell_slippage_halfSpread hf hm
  have : 0 < t.cost := by
    simp only [cost, hslip]
    have : 0 < -t.qty * t.spread := mul_pos (by linarith) hs
    linarith
  rw [net_eq_neg_cost]; linarith

/-! ### A classical trading system as a list of transactions -/

/-- The evaluation of a whole classical system: the sum of the evaluations of its transactions. -/
def sysNet (s : List Txn) : ℚ := (s.map Txn.net).sum

/-- The total friction of a classical system. -/
def sysCost (s : List Txn) : ℚ := (s.map Txn.cost).sum

/-- **The system is evaluated exactly as minus its friction.**  Local prices cancel transaction by
transaction, so the whole classical system reduces to its inf reading. -/
theorem sysNet_eq_neg_sysCost (s : List Txn) : sysNet s = -sysCost s := by
  induction s with
  | nil => simp [sysNet, sysCost]
  | cons t r ih => simp only [sysNet, sysCost, List.map_cons, List.sum_cons] at *
                   rw [ih, net_eq_neg_cost]; ring

/-- A classical system all of whose transactions charge cannot be profitable. -/
theorem sysNet_nonpos (s : List Txn) (h : ∀ t ∈ s, 0 ≤ t.cost) : sysNet s ≤ 0 := by
  rw [sysNet_eq_neg_sysCost, neg_nonpos]
  refine List.sum_nonneg ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact h t ht

/-- …and it is strictly loss-making as soon as one transaction actually charges. -/
theorem sysNet_neg_of_charge (s : List Txn) (h : ∀ t ∈ s, 0 ≤ t.cost) {t₀ : Txn} (ht₀ : t₀ ∈ s)
    (hpos : 0 < t₀.cost) : sysNet s < 0 := by
  rw [sysNet_eq_neg_sysCost, neg_lt_zero]
  have hmem : t₀.cost ∈ s.map Txn.cost := List.mem_map.2 ⟨t₀, ht₀, rfl⟩
  have hnn : ∀ x ∈ s.map Txn.cost, 0 ≤ x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact h t ht
  exact lt_of_lt_of_le hpos (List.single_le_sum hnn _ hmem)

/-! ## §5  The system on a value-flow network -/

section Network

variable {V : Type u}

/-- A cost cochain is **symmetric**: friction is paid in either direction. -/
def SymCost (c : Cochain V ℚ) : Prop := ∀ i j, c i j = c j i

/-- A cost cochain is **nonnegative**: no edge pays you to cross it. -/
def NonNegCost (c : Cochain V ℚ) : Prop := ∀ i j, 0 ≤ c i j

/-- The **trading cochain**: what an edge actually delivers is its price gain net of its friction. -/
def tradeCochain (w c : Cochain V ℚ) : Cochain V ℚ := fun i j => w i j - c i j

theorem hol_sub (w c : Cochain V ℚ) (i : V) (u : List V) :
    hol (tradeCochain w c) i u = hol w i u - hol c i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simp only [hol_cons, ih j, tradeCochain]; ring

/-- Friction accumulates: the holonomy of a nonnegative cost cochain is nonnegative. -/
theorem hol_cost_nonneg {c : Cochain V ℚ} (hc : NonNegCost c) (i : V) (u : List V) :
    0 ≤ hol c i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih => simpa using add_nonneg (hc i j) (ih j)

/-- Quantitatively: a circuit of `n` edges each charging at least `k` accumulates at least `n * k`. -/
theorem hol_cost_ge_len_mul {c : Cochain V ℚ} {k : ℚ} (hc : ∀ i j, k ≤ c i j) (i : V) (u : List V) :
    (u.length : ℚ) * k ≤ hol c i u := by
  induction u generalizing i with
  | nil => simp
  | cons j t ih =>
      have := ih j
      have hij := hc i j
      simp only [hol_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- **Prices are exact, so they vanish on circuits.**  This is the tokenomic statement: a price
field that admits a global token has no holonomy. -/
theorem price_loop_zero {N : Net V} (p : V → ℚ) (i : V) (u : List V) (hu : N.IsWalk i u)
    (hi : NRRF742.term i u = i) : hol (dOf p) i u = 0 :=
  hol_dOf_closed (N := N) p i u hu hi

/-- **The evaluation of the classical system around a circuit.**  With prices exact, the round trip
returns exactly minus the friction it paid. -/
theorem classical_roundTrip_eq_neg_cost {N : Net V} (p : V → ℚ) (c : Cochain V ℚ) (i : V)
    (u : List V) (hu : N.IsWalk i u) (hi : NRRF742.term i u = i) :
    hol (tradeCochain (dOf p) c) i u = -hol c i u := by
  rw [hol_sub, price_loop_zero (N := N) p i u hu hi, zero_sub]

/-- Hence a classical system can never make money on a circuit of an exact price field. -/
theorem classical_roundTrip_nonpos {N : Net V} {c : Cochain V ℚ} (hc : NonNegCost c) (p : V → ℚ)
    (i : V) (u : List V) (hu : N.IsWalk i u) (hi : NRRF742.term i u = i) :
    hol (tradeCochain (dOf p) c) i u ≤ 0 := by
  rw [classical_roundTrip_eq_neg_cost (N := N) p c i u hu hi, neg_nonpos]
  exact hol_cost_nonneg hc i u

/-- …and it loses strictly, in proportion to the length of the circuit, once every edge charges. -/
theorem classical_roundTrip_strict_loss {N : Net V} {c : Cochain V ℚ} {k : ℚ} (hk : 0 < k)
    (hc : ∀ i j, k ≤ c i j) (p : V → ℚ) (i : V) (u : List V) (hu : N.IsWalk i u)
    (hi : NRRF742.term i u = i) (hne : u ≠ []) :
    hol (tradeCochain (dOf p) c) i u ≤ -((u.length : ℚ) * k) ∧
      hol (tradeCochain (dOf p) c) i u < 0 := by
  have hlen : (1 : ℚ) ≤ (u.length : ℚ) := by
    have : 1 ≤ u.length := List.length_pos_iff.2 hne
    exact_mod_cast this
  have hb := hol_cost_ge_len_mul hc i u
  rw [classical_roundTrip_eq_neg_cost (N := N) p c i u hu hi]
  constructor
  · linarith
  · nlinarith

/-- **Profit is arbitrage, not trading.**  If a classical system makes money around a circuit while
paying nonnegative friction, then the price field itself already had holonomy on that circuit. -/
theorem profit_needs_arbitrage {N : Net V} {w c : Cochain V ℚ} (hc : NonNegCost c) (i : V)
    (u : List V) (hu : N.IsWalk i u) (hi : NRRF742.term i u = i)
    (hp : 0 < hol (tradeCochain w c) i u) : ¬ NoArbitrage N w := by
  intro hna
  have h0 : hol w i u = 0 := hna i u hu hi
  rw [hol_sub, h0] at hp
  have := hol_cost_nonneg hc i u
  linarith

/-- Equivalently: such a price field admits no global token at all. -/
theorem profit_needs_nonexact {N : Net V} {w c : Cochain V ℚ} (hc : NonNegCost c) (i : V)
    (u : List V) (hu : N.IsWalk i u) (hi : NRRF742.term i u = i)
    (hp : 0 < hol (tradeCochain w c) i u) : ¬ Glues N w :=
  fun hg => profit_needs_arbitrage hc i u hu hi hp (noArbitrage_of_glues hg)

/-- The exact criterion: a circuit pays exactly when its price holonomy beats its friction. -/
theorem profitable_iff_price_exceeds_cost (w c : Cochain V ℚ) (i : V) (u : List V) :
    0 < hol (tradeCochain w c) i u ↔ hol c i u < hol w i u := by
  rw [hol_sub, sub_pos]

end Network

/-! ## §6  The system in time: the classical P&L identity -/

/-- The classical profit and loss of a system holding `q i` over step `i` in a market marked at
`m`, paying `c i` on step `i`. -/
def pnl (q m c : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (q i * (m (i + 1) - m i) - c i)

/-- **The classical P&L identity.**  A constant position earns exactly position times price move,
less the accumulated cost. -/
theorem pnl_const_position {q m c : ℕ → ℚ} {Q : ℚ} (hq : ∀ i, q i = Q) (n : ℕ) :
    pnl q m c n = Q * (m n - m 0) - ∑ i ∈ Finset.range n, c i := by
  have h1 : ∑ i ∈ Finset.range n, (m (i + 1) - m i) = m n - m 0 := Finset.sum_range_sub m n
  simp only [pnl, hq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1]

/-- **A market that returns pays nothing back.**  If the mark returns to where it started, the whole
evaluation of the classical system is minus its accumulated cost. -/
theorem pnl_returning_market {q m c : ℕ → ℚ} {Q : ℚ} (hq : ∀ i, q i = Q) {n : ℕ}
    (hm : m n = m 0) : pnl q m c n = -∑ i ∈ Finset.range n, c i := by
  rw [pnl_const_position hq, hm]; ring

/-- …which is never positive when the costs are. -/
theorem pnl_returning_nonpos {q m c : ℕ → ℚ} {Q : ℚ} (hq : ∀ i, q i = Q) {n : ℕ}
    (hm : m n = m 0) (hc : ∀ i, 0 ≤ c i) : pnl q m c n ≤ 0 := by
  rw [pnl_returning_market hq hm, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => hc i

/-- A classical run is profitable exactly when the price move beats the accumulated cost. -/
theorem pnl_pos_iff {q m c : ℕ → ℚ} {Q : ℚ} (hq : ∀ i, q i = Q) (n : ℕ) :
    0 < pnl q m c n ↔ ∑ i ∈ Finset.range n, c i < Q * (m n - m 0) := by
  rw [pnl_const_position hq, sub_pos]

/-! ## §7  Execution is a rigid relational determination -/

/-- Which side of the book the order takes. -/
inductive Side
  | buy
  | sell
  deriving DecidableEq, Repr

/-- The classical execution rule as a relation: a buy is filled at the ask, a sell at the bid. -/
def execRel (t : Txn) (s : Side) : Constraint ℚ :=
  fun _ x => x = match s with | .buy => t.ask | .sell => t.bid

theorem execRel_rigid (t : Txn) (s : Side) : Rigid (execRel t s) :=
  fun _ => ⟨_, rfl, fun _ h => h⟩

/-- The execution selected by NRRF775's natural form selector. -/
noncomputable def execSel (t : Txn) (s : Side) : ℕ → ℚ := sel (execRel t s) (execRel_rigid t s)

theorem execSel_buy (t : Txn) (n : ℕ) : execSel t .buy n = t.ask :=
  (sel_eq_of_admissible (execRel_rigid t .buy) (rfl : t.ask = t.ask)).symm

theorem execSel_sell (t : Txn) (n : ℕ) : execSel t .sell n = t.bid :=
  (sel_eq_of_admissible (execRel_rigid t .sell) (rfl : t.bid = t.bid)).symm

/-- The classical fill is the *unique* admissible execution: it is determined by the relation, not
chosen by the trader. -/
theorem execSel_unique (t : Txn) (s : Side) : ∃! f : ℕ → ℚ, ∀ n, execRel t s n (f n) :=
  NRRF775.naturalForm_exists_unique (execRel_rigid t s)

/-- Executing as selected, and marking at the mid, is exactly the crossing trade of §4. -/
theorem selected_execution_is_crossing {t : Txn} (hf : t.fill = execSel t .buy 0)
    (hm : t.mark = t.mid) (hq : 0 < t.qty) (hs : 0 < t.spread) (he : 0 ≤ t.fee) : t.net < 0 :=
  crossing_trade_strictly_negative (by rw [hf, execSel_buy]) hm hq hs he

/-! ## §8  The answer -/

/-- **NRRF780 — the classical trading system evaluated in the relative unity of value flow.**

1. The six aspects of a classical transaction are a complete and irredundant multilayer form.
2. The inf reading (cost) is a translation of the local readings (prices) and strictly coarser.
3. A classical transaction is worth exactly minus its cost, and a system of them exactly minus their
   total cost.
4. Crossing the spread is strictly loss-making.
5. On a network with an exact price field, every circuit returns minus its friction; profit on a
   circuit forces the price field to carry holonomy — arbitrage, not trading.
6. In time, a market that returns to its mark returns to the trader minus the accumulated cost.
7. The classical fill is a rigid determination, not a preference. -/
theorem nrrf780_answer :
    NRRF772.Complete layer ∧
    ¬ NRRF772.Complete layerDropFill ∧
    NRRF772.Refines localRead Txn.cost ∧
    ¬ NRRF772.Refines Txn.cost localRead ∧
    (∀ t : Txn, t.net = -t.cost) ∧
    (∀ s : List Txn, sysNet s = -sysCost s) ∧
    (∀ t : Txn, t.fill = t.ask → t.mark = t.mid → 0 < t.qty → 0 < t.spread → 0 ≤ t.fee →
      t.net < 0) ∧
    (∀ (V : Type) (N : Net V) (p : V → ℚ) (c : Cochain V ℚ), NonNegCost c →
      ∀ (i : V) (u : List V), N.IsWalk i u → NRRF742.term i u = i →
        hol (tradeCochain (dOf p) c) i u = -hol c i u ∧
        hol (tradeCochain (dOf p) c) i u ≤ 0) ∧
    (∀ (V : Type) (N : Net V) (w c : Cochain V ℚ), NonNegCost c →
      ∀ (i : V) (u : List V), N.IsWalk i u → NRRF742.term i u = i →
        0 < hol (tradeCochain w c) i u → ¬ Glues N w) ∧
    (∀ (q m c : ℕ → ℚ) (Q : ℚ), (∀ i, q i = Q) → ∀ n, m n = m 0 → (∀ i, 0 ≤ c i) →
      pnl q m c n ≤ 0) ∧
    (∀ (t : Txn) (s : Side), ∃! f : ℕ → ℚ, ∀ n, execRel t s n (f n)) :=
  ⟨layers_complete, layers_drop_fill_not_complete, inf_refines_local, local_not_refines_inf,
   net_eq_neg_cost, sysNet_eq_neg_sysCost,
   fun _ hf hm hq hs he => crossing_trade_strictly_negative hf hm hq hs he,
   fun _ N p c hc i u hu hi =>
     ⟨classical_roundTrip_eq_neg_cost (N := N) p c i u hu hi,
      classical_roundTrip_nonpos (N := N) hc p i u hu hi⟩,
   fun _ _ _ _ hc i u hu hi hp => profit_needs_nonexact hc i u hu hi hp,
   fun _ _ _ _ hq _ hm hc => pnl_returning_nonpos hq hm hc,
   fun t s => execSel_unique t s⟩

/-! ## Audit -/

#print axioms net_eq_neg_cost
#print axioms layers_complete
#print axioms layers_drop_fill_not_complete
#print axioms inf_refines_local
#print axioms local_not_refines_inf
#print axioms transEq_flow_cost
#print axioms flow_cost_ratio_invariant
#print axioms crossing_trade_strictly_negative
#print axioms sysNet_eq_neg_sysCost
#print axioms classical_roundTrip_eq_neg_cost
#print axioms classical_roundTrip_strict_loss
#print axioms profit_needs_nonexact
#print axioms pnl_returning_market
#print axioms execSel_unique
#print axioms nrrf780_answer

end NRRF780
