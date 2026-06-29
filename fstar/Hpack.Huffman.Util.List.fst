module Hpack.Huffman.Util.List

/// Generic, RFC-agnostic list lemmas shared across the proof. Nothing here
/// mentions the code table:
///   * `all_pred`/`all_pred_index` — "every element satisfies `f`" together with
///     its per-index consequence, the single combinator behind every element-wise
///     table fact (codes fit their length, lengths in range, …).

module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1"

(* ---------------------------------------------------------------------- *)
(* element-wise predicate ⟹ per-index fact                                *)
(* ---------------------------------------------------------------------- *)

(* `all_pred` is the transparent definition exposed in the interface. *)

/// Per-index consequence (one proof for every element-wise table fact:
/// instantiate `f` — codes fit, lengths positive, lengths ≤ 30, … — and the
/// matching `*_index` lemma is just `all_pred_index f`).
let rec all_pred_index (#a:Type) (f:a -> bool) (l:list a) (i:nat{i < L.length l})
  : Lemma (requires all_pred f l) (ensures f (L.index l i)) (decreases l)
  = match l with x :: tl -> if i = 0 then () else all_pred_index f tl (i - 1)
