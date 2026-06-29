module Hpack.Huffman.Table.Properties

/// The RFC 7541 Appendix B invariants, proved over the concrete code table by
/// normalisation. Verifying this module *is* the validation of the
/// table data: nothing about the code is taken on faith.
///   * every code length is in [5, 30];
///   * the EOS symbol (256) is 0x3fffffff with length 30;
///   * the code is a prefix code (no code is a prefix of another), which in
///     particular makes all 257 codes distinct;
///   * each code fits in its own bit-length, and lengths are positive and ≤ 30.
///
/// Element-wise facts are phrased through the generic `all_pred` combinator, so a
/// single per-index lemma (`Hpack.Huffman.Util.List.all_pred_index`) serves them all.
/// Spot-value lemmas anchor concrete entries to independently-known RFC constants.

open Hpack.Huffman.Table
open FStar.Mul
module L = FStar.List.Tot
module Lst = Hpack.Huffman.Util.List

(* ---------------------------------------------------------------------- *)
(* Prefix-code property                                                   *)
(* ---------------------------------------------------------------------- *)

/// Codes are stored right-aligned. Reading bit strings MSB-first, the code of
/// `e1` (width `l1`) is a prefix of the code of `e2` (width `l2`) exactly when
/// `l1 <= l2` and the top `l1` bits of `e2` equal `e1`, i.e.
/// `e2.code / 2^(l2 - l1) = e1.code`. `no_prefix` says neither is a prefix of
/// the other. Two entries with the same length and code fail this check (one is
/// trivially a prefix of the other), so `no_prefix` also rules out duplicates.
let no_prefix (e1 e2:entry) : bool =
  if e1.len <= e2.len
  then e2.code / pow2 (e2.len - e1.len) <> e1.code
  else e1.code / pow2 (e1.len - e2.len) <> e2.code

let rec ok_against (e:entry) (rest:list entry) : bool =
  match rest with
  | [] -> true
  | x :: tl -> no_prefix e x && ok_against e tl

/// True iff no entry's code is a prefix of any other entry's code.
let rec prefix_free (l:list entry) : bool =
  match l with
  | [] -> true
  | x :: tl -> ok_against x tl && prefix_free tl

(* ---------------------------------------------------------------------- *)
(* Element-wise predicates (via the generic combinator)                   *)
(* ---------------------------------------------------------------------- *)

/// Code length within the RFC's [5, 30] band.
let len_in_range (e:entry) : bool = 5 <= e.len && e.len <= 30
/// Code fits in its own bit-length.
let fits (e:entry) : bool = e.code < pow2 e.len
/// Code length is positive (a fortiori true of the RFC's [5,30] lengths).
let pos_len (e:entry) : bool = e.len >= 1
/// Code length is at most 30.
let le30 (e:entry) : bool = e.len <= 30

(* ---------------------------------------------------------------------- *)
(* Proofs over the concrete table (discharged by normalisation)            *)
(* ---------------------------------------------------------------------- *)

/// The table has exactly 257 entries (bytes 0..255 plus EOS).
let lemma_table_complete () : Lemma (L.length hpack_table == 257) =
  assert_norm (L.length hpack_table == 257)

/// Every code length lies in [5, 30].
let lemma_lengths_in_range () : Lemma (Lst.all_pred len_in_range hpack_table) =
  assert_norm (Lst.all_pred len_in_range hpack_table)

/// The EOS symbol is code 0x3fffffff (= 1073741823) with length 30.
let lemma_eos_code () : Lemma (L.nth hpack_table eos_sym == Some (mk 1073741823 30)) =
  assert_norm (L.nth hpack_table eos_sym == Some (mk 1073741823 30))

/// The table is a prefix code (hence all codes are distinct).
let lemma_prefix_free () : Lemma (prefix_free hpack_table) =
  assert_norm (prefix_free hpack_table)

/// Every code fits in its own bit-length.
let lemma_all_fit () : Lemma (Lst.all_pred fits hpack_table) =
  assert_norm (Lst.all_pred fits hpack_table)

/// Every code length is positive.
let lemma_all_pos () : Lemma (Lst.all_pred pos_len hpack_table) =
  assert_norm (Lst.all_pred pos_len hpack_table)

/// Every code length is at most 30.
let lemma_all_le30 () : Lemma (Lst.all_pred le30 hpack_table) =
  assert_norm (Lst.all_pred le30 hpack_table)

(* ---------------------------------------------------------------------- *)
(* Prefix-freeness: structural property -> per-pair fact                   *)
(* ---------------------------------------------------------------------- *)

/// `ok_against e rest` gives `no_prefix e (rest[k])` for every k.
let rec ok_against_index (e:entry) (rest:list entry) (k:nat{k < L.length rest})
  : Lemma (requires ok_against e rest)
          (ensures no_prefix e (L.index rest k)) (decreases rest)
  = match rest with
    | x :: tl -> if k = 0 then () else ok_against_index e tl (k - 1)

/// `prefix_free l` gives `no_prefix l[i] l[j]` for every i < j.
let rec prefix_free_index (l:list entry) (i:nat) (j:nat{i < j /\ j < L.length l})
  : Lemma (requires prefix_free l)
          (ensures no_prefix (L.index l i) (L.index l j)) (decreases l)
  = match l with
    | x :: tl -> if i = 0 then ok_against_index x tl (j - 1)
                 else prefix_free_index tl (i - 1) (j - 1)

/// `no_prefix` is symmetric (it always compares the shorter code's bits).
let no_prefix_sym (e1 e2:entry)
  : Lemma (no_prefix e1 e2 == no_prefix e2 e1) = ()

(* ---------------------------------------------------------------------- *)
(* RFC spot-value anchors                                                  *)
(* ---------------------------------------------------------------------- *)

/// Pin specific entries to independently-known RFC 7541 Appendix B values. The
/// structural lemmas above prove the table is a *valid* prefix code, but not that
/// it is *the RFC's* code; these anchors tie concrete entries to spec constants,
/// so a transcription drift on a common symbol fails verification.
let lemma_rfc_spot_values () : Lemma (
  L.nth hpack_table 48  == Some (mk 0 5)    /\  (* '0' *)
  L.nth hpack_table 49  == Some (mk 1 5)    /\  (* '1' *)
  L.nth hpack_table 50  == Some (mk 2 5)    /\  (* '2' *)
  L.nth hpack_table 97  == Some (mk 3 5)    /\  (* 'a' *)
  L.nth hpack_table 99  == Some (mk 4 5)    /\  (* 'c' *)
  L.nth hpack_table 101 == Some (mk 5 5)    /\  (* 'e' *)
  L.nth hpack_table 105 == Some (mk 6 5)    /\  (* 'i' *)
  L.nth hpack_table 111 == Some (mk 7 5)    /\  (* 'o' *)
  L.nth hpack_table 115 == Some (mk 8 5)    /\  (* 's' *)
  L.nth hpack_table 116 == Some (mk 9 5)    /\  (* 't' *)
  L.nth hpack_table 32  == Some (mk 20 6)   /\  (* ' '  = 0x14   *)
  L.nth hpack_table 33  == Some (mk 1016 10)    (* '!'  = 0x3f8  *)
) =
  assert_norm (
    L.nth hpack_table 48  == Some (mk 0 5)    /\
    L.nth hpack_table 49  == Some (mk 1 5)    /\
    L.nth hpack_table 50  == Some (mk 2 5)    /\
    L.nth hpack_table 97  == Some (mk 3 5)    /\
    L.nth hpack_table 99  == Some (mk 4 5)    /\
    L.nth hpack_table 101 == Some (mk 5 5)    /\
    L.nth hpack_table 105 == Some (mk 6 5)    /\
    L.nth hpack_table 111 == Some (mk 7 5)    /\
    L.nth hpack_table 115 == Some (mk 8 5)    /\
    L.nth hpack_table 116 == Some (mk 9 5)    /\
    L.nth hpack_table 32  == Some (mk 20 6)   /\
    L.nth hpack_table 33  == Some (mk 1016 10))
