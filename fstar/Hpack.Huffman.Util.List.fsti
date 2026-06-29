module Hpack.Huffman.Util.List

/// Generic, RFC-agnostic list toolkit. `all_pred f l` is "every element of `l`
/// satisfies `f`"; `all_pred_index` is its per-index consequence — the single
/// combinator behind every element-wise table fact (codes fit their length,
/// lengths in range, …). The predicate is exposed transparently (callers compute
/// it, typically by `assert_norm`); the lemma's proof is sealed.

module L = FStar.List.Tot

/// Structural "every element of `l` satisfies `f`".
let rec all_pred (#a:Type) (f:a -> bool) (l:list a) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | x :: tl -> f x && all_pred f tl

/// Per-index consequence: if every element satisfies `f`, so does element `i`.
val all_pred_index (#a:Type) (f:a -> bool) (l:list a) (i:nat{i < L.length l})
  : Lemma (requires all_pred f l) (ensures f (L.index l i))
