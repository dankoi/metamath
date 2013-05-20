type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type atoms (* AXIOM TO BE REALIZED *)

type formula =
| Atom of atoms
| Bot
| Func of formula * formula
| Sum of formula * formula

type context = formula list

type proof =
| Inl0 of context * bool * formula * formula * proof
| Inr0 of context * bool * formula * formula * proof
| Lam of formula list * bool * formula * formula * proof
| Hyp of formula list * bool * formula
| Wkn of context * bool * formula * formula * proof
| Case of context * bool * formula * formula * formula * proof * proof
   * proof
| App of context * bool * formula * formula * proof * proof
| Reset of context * bool * proof
| Shift of formula list * formula * proof

type proof_nf =
| Nf_Inl of context * bool * formula * formula * proof_nf
| Nf_Inr of context * bool * formula * formula * proof_nf
| Nf_Lam of formula list * bool * formula * formula * proof_nf
| Nf_ne of context * bool * formula * proof_ne
| Nf_Shift of formula list * formula * proof_nf
and proof_ne =
| Ne_Hyp of formula list * bool * formula
| Ne_Case of context * bool * formula * formula * formula * proof_ne
   * proof_nf * proof_nf
| Ne_App of context * bool * formula * formula * proof_ne * proof_nf
| Ne_Reset of context * bool * proof_ne
| Ne_Wkn of context * bool * formula * formula * proof_nf

type prefix =
| Prefix_refl of context
| Prefix_cons of context * context * formula * prefix

(** val prefix_trans :
    context -> context -> context -> prefix -> prefix -> prefix **)

let rec prefix_trans w w' w'' h = function
| Prefix_refl w0 -> h
| Prefix_cons (w0, w'0, a, p) ->
  Prefix_cons (w, w'0, a, (prefix_trans w w0 w'0 h p))

(** val proof_nf_mon :
    context -> context -> prefix -> formula -> bool -> proof_nf -> proof_nf **)

let rec proof_nf_mon c c0 p a a0 r =
  match p with
  | Prefix_refl w -> r
  | Prefix_cons (w, w', a1, p0) ->
    Nf_ne ((Cons (a1, w')), a0, a, (Ne_Wkn (w', a0, a, a1,
      (proof_nf_mon w w' p0 a a0 r))))

(** val proof_ne_mon :
    context -> context -> prefix -> formula -> bool -> proof_ne -> proof_ne **)

let rec proof_ne_mon c c0 p a a0 r =
  match p with
  | Prefix_refl w -> r
  | Prefix_cons (w, w', a1, p0) ->
    Ne_Wkn (w', a0, a, a1, (Nf_ne (w', a0, a,
      (proof_ne_mon w w' p0 a a0 r))))

(** val proof_nf_mon2 :
    formula -> context -> bool -> proof_nf -> bool -> proof_nf **)

let rec proof_nf_mon2 a gamma annot p annot' =
  let rec f c b f0 p0 annot'0 =
    match p0 with
    | Nf_Inl (gamma0, annot0, a0, b0, p1) ->
      Nf_Inl (gamma0, annot'0, a0, b0, (f gamma0 annot0 a0 p1 annot'0))
    | Nf_Inr (gamma0, annot0, a0, b0, p1) ->
      Nf_Inr (gamma0, annot'0, a0, b0, (f gamma0 annot0 b0 p1 annot'0))
    | Nf_Lam (gamma0, annot0, a0, b0, p1) ->
      Nf_Lam (gamma0, annot'0, a0, b0,
        (f (Cons (a0, gamma0)) annot0 b0 p1 annot'0))
    | Nf_ne (gamma0, annot0, a0, p1) ->
      Nf_ne (gamma0, annot'0, a0,
        (proof_ne_mon2 a0 gamma0 annot0 p1 annot'0))
    | Nf_Shift (gamma0, a0, p1) ->
      Nf_Shift (gamma0, a0,
        (proof_nf_mon2 Bot (Cons ((Func (a0, Bot)), gamma0)) True p1 True))
  in f gamma annot a p annot'

(** val proof_ne_mon2 :
    formula -> context -> bool -> proof_ne -> bool -> proof_ne **)

and proof_ne_mon2 a gamma annot p annot' =
  let rec f c b f0 p0 annot'0 =
    match p0 with
    | Ne_Hyp (gamma0, annot0, a0) -> Ne_Hyp (gamma0, annot'0, a0)
    | Ne_Case (gamma0, annot0, a0, b0, c0, p1, p2, p3) ->
      Ne_Case (gamma0, annot'0, a0, b0, c0,
        (f gamma0 annot0 (Sum (a0, b0)) p1 annot'0),
        (proof_nf_mon2 c0 (Cons (a0, gamma0)) annot0 p2 annot'0),
        (proof_nf_mon2 c0 (Cons (b0, gamma0)) annot0 p3 annot'0))
    | Ne_App (gamma0, annot0, a0, b0, p1, p2) ->
      Ne_App (gamma0, annot'0, a0, b0,
        (f gamma0 annot0 (Func (a0, b0)) p1 annot'0),
        (proof_nf_mon2 a0 gamma0 annot0 p2 annot'0))
    | Ne_Reset (gamma0, annot0, p1) ->
      Ne_Reset (gamma0, annot'0, (f gamma0 True Bot p1 True))
    | Ne_Wkn (gamma0, annot0, a0, b0, p1) ->
      Ne_Wkn (gamma0, annot'0, a0, b0,
        (proof_nf_mon2 a0 gamma0 annot0 p1 annot'0))
  in f gamma annot a p annot'

module type Kripke_structure = 
 sig 
  type coq_K 
  
  type wle 
  
  val wle_refl : coq_K -> wle
  
  val wle_trans : coq_K -> coq_K -> coq_K -> wle -> wle -> wle
  
  type coq_X 
  
  val coq_X_mon : coq_K -> bool -> formula -> coq_X -> coq_K -> wle -> coq_X
  
  val coq_X_mon2 : coq_K -> bool -> formula -> coq_X -> bool -> coq_X
  
  val coq_X_reset : coq_K -> bool -> coq_X -> coq_X
 end

module Kripke_structure_monad = 
 functor (Coq_ks:Kripke_structure) ->
 struct 
  type 'f coq_Kont = __
  
  (** val coq_Kont_mon :
      Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
      Coq_ks.wle -> 'a1 coq_Kont **)
  
  let coq_Kont_mon w annot a h w' ww' =
    match annot with
    | True ->
      Obj.magic (fun w'' w'w'' k ->
        Obj.magic h w'' (Coq_ks.wle_trans w w' w'' ww' w'w'') k)
    | False ->
      Obj.magic (fun c w'' w'w'' k ->
        Obj.magic h c w'' (Coq_ks.wle_trans w w' w'' ww' w'w'') k)
 end

module Coq_forcing_generic_properties = 
 functor (Coq_ks:Kripke_structure) ->
 functor (Coq_sforces_implementation:sig 
  module Coq_ks_monad : 
   sig 
    type 'f coq_Kont = __
    
    val coq_Kont_mon :
      Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
      Coq_ks.wle -> 'a1 coq_Kont
   end
  
  type sforces 
  
  val sforces_mon :
    formula -> Coq_ks.coq_K -> bool -> sforces -> Coq_ks.coq_K -> Coq_ks.wle
    -> sforces
  
  val sforces_mon2 : formula -> Coq_ks.coq_K -> sforces -> sforces
  
  val coq_Kont_sforces_mon2 :
    Coq_ks.coq_K -> bool -> formula -> sforces Coq_ks_monad.coq_Kont -> bool
    -> sforces Coq_ks_monad.coq_Kont
 end) ->
 struct 
  module Coq_ks_monad = Kripke_structure_monad(Coq_ks)
  
  (** val ret :
      Coq_ks.coq_K -> bool -> formula -> Coq_sforces_implementation.sforces
      -> Coq_sforces_implementation.sforces
      Coq_sforces_implementation.Coq_ks_monad.coq_Kont **)
  
  let ret w annot a h =
    match annot with
    | True ->
      Obj.magic (fun w1 wle1 k1 ->
        k1 w1 (Coq_ks.wle_refl w1)
          (Coq_sforces_implementation.sforces_mon a w True h w1 wle1))
    | False ->
      Obj.magic (fun c w1 ww1 k ->
        k w1 (Coq_ks.wle_refl w1)
          (Coq_sforces_implementation.sforces_mon a w False h w1 ww1))
  
  (** val bind :
      Coq_ks.coq_K -> bool -> formula -> formula -> (Coq_ks.coq_K ->
      Coq_ks.wle -> Coq_sforces_implementation.sforces ->
      Coq_sforces_implementation.sforces
      Coq_sforces_implementation.Coq_ks_monad.coq_Kont) ->
      Coq_sforces_implementation.sforces
      Coq_sforces_implementation.Coq_ks_monad.coq_Kont ->
      Coq_sforces_implementation.sforces
      Coq_sforces_implementation.Coq_ks_monad.coq_Kont **)
  
  let bind w annot a b f a0 =
    match annot with
    | True ->
      Obj.magic (fun w1 wle1 k1 ->
        Obj.magic a0 w1 wle1 (fun w2 wle2 a2 ->
          Obj.magic f w2 (Coq_ks.wle_trans w w1 w2 wle1 wle2) a2 w2
            (Coq_ks.wle_refl w2) (fun w3 wle3 b3 ->
            k1 w3 (Coq_ks.wle_trans w1 w2 w3 wle2 wle3) b3)))
    | False ->
      Obj.magic (fun c1 w1 wle1 k1 ->
        Obj.magic a0 c1 w1 wle1 (fun w2 wle2 a2 ->
          Obj.magic f w2 (Coq_ks.wle_trans w w1 w2 wle1 wle2) a2 c1 w2
            (Coq_ks.wle_refl w2) (fun w3 wle3 b3 ->
            k1 w3 (Coq_ks.wle_trans w1 w2 w3 wle2 wle3) b3)))
  
  type sforces_cxt = __
  
  (** val sforces_cxt_mon :
      context -> Coq_ks.coq_K -> bool -> sforces_cxt -> Coq_ks.coq_K ->
      Coq_ks.wle -> sforces_cxt **)
  
  let rec sforces_cxt_mon l w annot h w' h0 =
    match l with
    | Nil -> h
    | Cons (y, l0) ->
      let Pair (s, s0) = Obj.magic h in
      Obj.magic (Pair
        ((Coq_sforces_implementation.sforces_mon y w annot s w' h0),
        (sforces_cxt_mon l0 w annot s0 w' h0)))
  
  (** val sforces_cxt_mon2 :
      context -> Coq_ks.coq_K -> bool -> sforces_cxt -> bool -> sforces_cxt **)
  
  let rec sforces_cxt_mon2 l w annot h annot' =
    match l with
    | Nil -> h
    | Cons (y, l0) ->
      let Pair (s, s0) = Obj.magic h in
      Obj.magic (Pair
        ((match annot' with
          | True ->
            (match annot with
             | True -> s
             | False -> Coq_sforces_implementation.sforces_mon2 y w s)
          | False ->
            (match annot with
             | True -> Obj.magic (fun _ t -> t)
             | False -> s)), (sforces_cxt_mon2 l0 w annot s0 annot')))
  
  type coq_Kont_cxt = __
  
  (** val coq_Kont_cxt_mon :
      context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> Coq_ks.coq_K ->
      Coq_ks.wle -> coq_Kont_cxt **)
  
  let rec coq_Kont_cxt_mon l w annot h w' h0 =
    match l with
    | Nil -> h
    | Cons (y, l0) ->
      let Pair (k, k0) = Obj.magic h in
      Obj.magic (Pair
        ((Coq_sforces_implementation.Coq_ks_monad.coq_Kont_mon w annot y k w'
           h0), (coq_Kont_cxt_mon l0 w annot k0 w' h0)))
  
  (** val coq_Kont_sforces_cxt_mon2 :
      context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> bool -> coq_Kont_cxt **)
  
  let rec coq_Kont_sforces_cxt_mon2 l w annot h annot' =
    match l with
    | Nil -> h
    | Cons (y, l0) ->
      let Pair (k, k0) = Obj.magic h in
      Obj.magic (Pair
        ((match annot' with
          | True ->
            (match annot with
             | True -> k
             | False ->
               Coq_sforces_implementation.coq_Kont_sforces_mon2 w False y k
                 True)
          | False ->
            (match annot with
             | True -> Obj.magic (fun c w1 h0 x0 _ t -> t)
             | False -> k)),
        (coq_Kont_sforces_cxt_mon2 l0 w annot k0 annot')))
 end

module Coq_sforces_cbv = 
 functor (Coq_ks:Kripke_structure) ->
 struct 
  module Coq_ks_monad = Kripke_structure_monad(Coq_ks)
  
  type sforces = __
  
  (** val sforces_mon :
      formula -> Coq_ks.coq_K -> bool -> sforces -> Coq_ks.coq_K ->
      Coq_ks.wle -> sforces **)
  
  let rec sforces_mon f w annot h w' h0 =
    match f with
    | Func (f0, f1) ->
      Obj.magic (fun w'0 h1 annot' _ x0 ->
        Obj.magic h w'0 (Coq_ks.wle_trans w w' w'0 h0 h1) annot' __ x0)
    | Sum (f0, f1) ->
      (match Obj.magic h with
       | Inl h' -> Obj.magic (Inl (sforces_mon f0 w annot h' w' h0))
       | Inr h' -> Obj.magic (Inr (sforces_mon f1 w annot h' w' h0)))
    | x -> Obj.magic (Coq_ks.coq_X_mon w annot x (Obj.magic h) w' h0)
  
  (** val sforces_mon2 : formula -> Coq_ks.coq_K -> sforces -> sforces **)
  
  let rec sforces_mon2 f w h =
    match f with
    | Func (f0, f1) ->
      Obj.magic (fun w' ww' annot' _ -> Obj.magic h w' ww' annot' __)
    | Sum (f0, f1) ->
      (match Obj.magic h with
       | Inl s -> Obj.magic (Inl (sforces_mon2 f0 w s))
       | Inr s -> Obj.magic (Inr (sforces_mon2 f1 w s)))
    | x -> Obj.magic (Coq_ks.coq_X_mon2 w False x (Obj.magic h) True)
  
  (** val coq_Kont_sforces_mon2 :
      Coq_ks.coq_K -> bool -> formula -> sforces Coq_ks_monad.coq_Kont ->
      bool -> sforces Coq_ks_monad.coq_Kont **)
  
  let coq_Kont_sforces_mon2 w annot a h annot' =
    match annot with
    | True ->
      (match annot' with
       | True -> h
       | False -> Obj.magic (fun c w1 h0 x0 _ t -> t))
    | False ->
      (match annot' with
       | True ->
         Obj.magic (fun w'' w'w'' k ->
           Coq_ks.coq_X_mon2 w'' False Bot
             (Obj.magic h Bot w'' w'w'' (fun w2 w''w2 hA ->
               Coq_ks.coq_X_reset w2 False
                 (k w2 w''w2 (sforces_mon2 a w2 hA)))) True)
       | False -> h)
  
  (** val run :
      Coq_ks.coq_K -> bool -> sforces Coq_ks_monad.coq_Kont -> Coq_ks.coq_X **)
  
  let run w annot h =
    match annot with
    | True -> Obj.magic h w (Coq_ks.wle_refl w) (fun w2 h0 h1 -> h1)
    | False -> Obj.magic h Bot w (Coq_ks.wle_refl w) (fun w2 h0 h1 -> h1)
 end

module Soundness = 
 functor (Coq_ks:Kripke_structure) ->
 struct 
  module Coq_ks_monad = Kripke_structure_monad(Coq_ks)
  
  module Coq_cbv_validity = Coq_sforces_cbv(Coq_ks)
  
  module Coq_generic_properties = Coq_forcing_generic_properties(Coq_ks)(Coq_cbv_validity)
  
  (** val soundness :
      context -> bool -> formula -> proof -> Coq_ks.coq_K -> bool ->
      Coq_generic_properties.sforces_cxt -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont **)
  
  let rec soundness c b f p w annot' h' =
    match p with
    | Inl0 (gamma, annot, a, b0, p0) ->
      Coq_generic_properties.bind w annot' a (Sum (a, b0)) (fun w' h x0 ->
        Coq_generic_properties.ret w' annot' (Sum (a, b0))
          (Obj.magic (Inl x0))) (soundness gamma annot a p0 w annot' h')
    | Inr0 (gamma, annot, a, b0, p0) ->
      Coq_generic_properties.bind w annot' b0 (Sum (a, b0)) (fun w' h x0 ->
        Coq_generic_properties.ret w' annot' (Sum (a, b0))
          (Obj.magic (Inr x0))) (soundness gamma annot b0 p0 w annot' h')
    | Lam (gamma, annot, a, b0, p0) ->
      Coq_generic_properties.ret w annot' (Func (a, b0))
        (Obj.magic (fun w1 wle1 annot1 _ h1 ->
          Obj.magic (fun w0 annot'0 _ h'0 ->
            soundness (Cons (a, gamma)) annot b0 p0 w0 annot'0 h'0) w1 annot1
            __ (Pair (h1,
            (Coq_generic_properties.sforces_cxt_mon gamma w annot1
              (Coq_generic_properties.sforces_cxt_mon2 gamma w annot' h'
                annot1) w1 wle1)))))
    | Hyp (gamma, annot, a) ->
      let Pair (ha, hGamma) = Obj.magic h' in
      Coq_generic_properties.ret w annot' a ha
    | Wkn (gamma, annot, a, b0, p0) ->
      let Pair (wB, wG) = Obj.magic h' in
      soundness gamma annot a p0 w annot' wG
    | Case (gamma, annot, a, b0, c0, p0, p1, p2) ->
      Coq_generic_properties.bind w annot' (Sum (a, b0)) c0
        (fun w1 wle1 h1 ->
        match Obj.magic h1 with
        | Inl s ->
          Obj.magic (fun w0 annot'0 _ h'0 ->
            soundness (Cons (a, gamma)) annot c0 p1 w0 annot'0 h'0) w1 annot'
            __ (Pair (s,
            (Coq_generic_properties.sforces_cxt_mon gamma w annot' h' w1
              wle1)))
        | Inr s ->
          Obj.magic (fun w0 annot'0 _ h'0 ->
            soundness (Cons (b0, gamma)) annot c0 p2 w0 annot'0 h'0) w1
            annot' __ (Pair (s,
            (Coq_generic_properties.sforces_cxt_mon gamma w annot' h' w1
              wle1)))) (soundness gamma annot (Sum (a, b0)) p0 w annot' h')
    | App (gamma, annot, a, b0, p0, p1) ->
      Coq_generic_properties.bind w annot' (Func (a, b0)) b0
        (fun w1 wle1 h1 ->
        Coq_generic_properties.bind w1 annot' a b0 (fun w2 wle2 h2 ->
          Obj.magic h1 w2 wle2 annot' __ h2)
          (soundness gamma annot a p1 w1 annot'
            (Coq_generic_properties.sforces_cxt_mon gamma w annot' h' w1
              wle1))) (soundness gamma annot (Func (a, b0)) p0 w annot' h')
    | Reset (gamma, annot, p0) ->
      Coq_generic_properties.ret w annot' Bot
        (match annot' with
         | True ->
           Obj.magic
             (Coq_cbv_validity.run w True
               (soundness gamma True Bot p0 w True h'))
         | False ->
           Obj.magic
             (Coq_ks.coq_X_reset w False
               (Coq_cbv_validity.run w True
                 (soundness gamma True Bot p0 w True
                   (Coq_generic_properties.sforces_cxt_mon2 gamma w False h'
                     True)))))
    | Shift (gamma, a, p0) ->
      let x0 = fun w1 ww1 kK ->
        Coq_cbv_validity.run w1 True
          (Obj.magic (fun w0 annot'0 _ h'0 ->
            soundness (Cons ((Func (a, Bot)), gamma)) True Bot p0 w0 annot'0
              h'0) w1 True __ (Pair ((fun w2 w1w2 annot'' _ hA ->
            Coq_generic_properties.ret w2 True Bot (kK w2 w1w2 hA)),
            (Coq_generic_properties.sforces_cxt_mon gamma w True h' w1 ww1))))
      in
      (fun w1 -> Obj.magic x0 w1)
 end

module Completeness = 
 struct 
  module U = 
   struct 
    type coq_K = context
    
    type wle = prefix
    
    (** val wle_refl : context -> prefix **)
    
    let wle_refl x =
      Prefix_refl x
    
    (** val wle_trans :
        context -> context -> context -> prefix -> prefix -> prefix **)
    
    let wle_trans =
      prefix_trans
    
    type coq_X = __
    
    (** val coq_X_mon :
        context -> bool -> formula -> coq_X -> context -> wle -> coq_X **)
    
    let coq_X_mon w annot a h w' ww' =
      match a with
      | Atom a0 ->
        Obj.magic (proof_ne_mon w w' ww' (Atom a0) annot (Obj.magic h))
      | Bot -> Obj.magic (proof_ne_mon w w' ww' Bot annot (Obj.magic h))
      | x -> Obj.magic (proof_nf_mon w w' ww' x annot (Obj.magic h))
    
    (** val coq_X_mon2 :
        context -> bool -> formula -> coq_X -> bool -> coq_X **)
    
    let coq_X_mon2 w annot a h annot' =
      match a with
      | Atom a0 ->
        Obj.magic (proof_ne_mon2 (Atom a0) w annot (Obj.magic h) annot')
      | Bot -> Obj.magic (proof_ne_mon2 Bot w annot (Obj.magic h) annot')
      | x -> Obj.magic (proof_nf_mon2 x w annot (Obj.magic h) annot')
    
    (** val coq_X_reset : context -> bool -> proof_ne -> proof_ne **)
    
    let coq_X_reset w annot h =
      Ne_Reset (w, annot, h)
   end
  
  module Coq_ks_monad = Kripke_structure_monad(U)
  
  module Coq_cbv_validity = Coq_sforces_cbv(U)
  
  module Coq_generic_properties = Coq_forcing_generic_properties(U)(Coq_cbv_validity)
  
  (** val completeness :
      formula -> context -> bool -> (Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont -> proof_nf, proof_ne ->
      Coq_cbv_validity.sforces Coq_cbv_validity.Coq_ks_monad.coq_Kont) prod **)
  
  let rec completeness = function
  | Atom a ->
    (fun w annot -> Pair ((fun h ->
      match annot with
      | True ->
        Nf_Shift (w, (Atom a), (Nf_ne ((Cons ((Func ((Atom a), Bot)), w)),
          True, Bot,
          (Obj.magic h (Cons ((Func ((Atom a), Bot)), w)) (Prefix_cons (w, w,
            (Func ((Atom a), Bot)), (Prefix_refl w))) (fun w2 hincl2 hatom ->
            Ne_App (w2, True, (Atom a), Bot,
            (proof_ne_mon (Cons ((Func ((Atom a), Bot)), w)) w2 hincl2 (Func
              ((Atom a), Bot)) True (Ne_Hyp (w, True, (Func ((Atom a),
              Bot))))), (Nf_ne (w2, True, (Atom a), hatom))))))))
      | False ->
        Nf_ne (w, False, (Atom a),
          (Obj.magic h (Atom a) w (U.wle_refl w) (fun w2 h0 x0 -> x0)))),
      (fun e -> Coq_generic_properties.ret w annot (Atom a) (Obj.magic e))))
  | Bot ->
    (fun w annot -> Pair ((fun c ->
      match annot with
      | True ->
        Nf_ne (w, True, Bot,
          (Obj.magic c w (U.wle_refl w) (fun w2 h h0 -> h0)))
      | False ->
        Nf_ne (w, False, Bot,
          (Obj.magic c Bot w (U.wle_refl w) (fun w2 h h0 -> h0)))), (fun e ->
      Coq_generic_properties.ret w annot Bot (Obj.magic e))))
  | Func (f0, f1) ->
    let iHA1 = completeness f0 in
    let iHA2 = completeness f1 in
    (fun w annot -> Pair ((fun h -> Nf_Lam (w, annot, f0, f1,
    (let h0 = fun w0 annot0 -> let Pair (x, x0) = iHA2 w0 annot0 in x in
     Obj.magic h0 (Cons (f0, w)) annot (fun w1 incl1 k1 ->
       match annot with
       | True ->
         let h1 = let Pair (x, x0) = iHA1 w1 True in x0 in
         Obj.magic h1
           (proof_ne_mon (Cons (f0, w)) w1 incl1 f0 True (Ne_Hyp (w, True,
             f0))) w1 (U.wle_refl w1) (fun w2 incl2 h2 ->
           Obj.magic h w2
             (U.wle_trans w w1 w2
               (U.wle_trans w (Cons (f0, w)) w1 (Prefix_cons (w, w, f0,
                 (Prefix_refl w))) incl1) incl2) (fun w3 incl3 f3 ->
             f3 w3 (U.wle_refl w3) True __
               (Coq_cbv_validity.sforces_mon f0 w2 True h2 w3 incl3) w3
               (U.wle_refl w3) (fun w4 incl4 h4 ->
               k1 w4
                 (U.wle_trans w1 w3 w4 (U.wle_trans w1 w2 w3 incl2 incl3)
                   incl4) h4)))
       | False ->
         (fun k2 ->
           let Pair (x, x0) = Obj.magic iHA1 incl1 False in
           x0
             (proof_ne_mon (Cons (f0, w)) (Obj.magic incl1) (Obj.magic k1) f0
               False (Ne_Hyp (w, False, f0))) w1 incl1 (Prefix_refl
             (Obj.magic incl1)) (fun w2 incl2 h2 ->
             Obj.magic h w1 w2
               (U.wle_trans w (Obj.magic incl1) w2
                 (U.wle_trans w (Cons (f0, w)) (Obj.magic incl1) (Prefix_cons
                   (w, w, f0, (Prefix_refl w))) (Obj.magic k1)) incl2)
               (fun w3 incl3 f3 ->
               f3 w3 (U.wle_refl w3) False __
                 (Coq_cbv_validity.sforces_mon f0 w2 False h2 w3 incl3) w1 w3
                 (U.wle_refl w3) (fun w4 incl4 h4 ->
                 k2 w4
                   (U.wle_trans (Obj.magic incl1) w3 w4
                     (U.wle_trans (Obj.magic incl1) w2 w3 incl2 incl3) incl4)
                   h4)))))))), (fun e ->
    Coq_generic_properties.ret w annot (Func (f0, f1))
      (Obj.magic (fun w' incl' annot' _ h' ->
        let h'0 = Coq_generic_properties.ret w' annot' f0 h' in
        let h = let Pair (x, x0) = iHA1 w' annot' in x in
        let h'1 = h h'0 in
        let Pair (x, x0) = iHA2 w' annot' in
        x0 (Ne_App (w', annot', f0, f1,
          (proof_ne_mon w w' incl' (Func (f0, f1)) annot'
            (proof_ne_mon2 (Func (f0, f1)) w annot e annot')), h'1)))))))
  | Sum (f0, f1) ->
    let iHA1 = completeness f0 in
    let iHA2 = completeness f1 in
    (fun w annot -> Pair ((fun h ->
    match annot with
    | True ->
      Nf_Shift (w, (Sum (f0, f1)), (Nf_ne ((Cons ((Func ((Sum (f0, f1)),
        Bot)), w)), True, Bot,
        (Obj.magic h (Cons ((Func ((Sum (f0, f1)), Bot)), w)) (Prefix_cons
          (w, w, (Func ((Sum (f0, f1)), Bot)), (Prefix_refl w)))
          (fun w1 incl1 h1 ->
          match h1 with
          | Inl h11 ->
            Ne_App (w1, True, (Sum (f0, f1)), Bot,
              (proof_ne_mon (Cons ((Func ((Sum (f0, f1)), Bot)), w)) w1 incl1
                (Func ((Sum (f0, f1)), Bot)) True (Ne_Hyp (w, True, (Func
                ((Sum (f0, f1)), Bot))))), (Nf_Inl (w1, True, f0, f1,
              (let annot0 = True in
               let Pair (x, x0) = iHA1 w1 annot0 in
               x (Coq_generic_properties.ret w1 True f0 h11)))))
          | Inr h12 ->
            Ne_App (w1, True, (Sum (f0, f1)), Bot,
              (proof_ne_mon (Cons ((Func ((Sum (f0, f1)), Bot)), w)) w1 incl1
                (Func ((Sum (f0, f1)), Bot)) True (Ne_Hyp (w, True, (Func
                ((Sum (f0, f1)), Bot))))), (Nf_Inr (w1, True, f0, f1,
              (let annot0 = True in
               let Pair (x, x0) = iHA2 w1 annot0 in
               x (Coq_generic_properties.ret w1 True f1 h12))))))))))
    | False ->
      Obj.magic h (Sum (f0, f1)) w (U.wle_refl w) (fun w1 incl1 h1 ->
        match h1 with
        | Inl h11 ->
          Nf_Inl (w1, False, f0, f1,
            (let annot0 = False in
             let Pair (x, x0) = iHA1 w1 annot0 in
             x (Coq_generic_properties.ret w1 False f0 h11)))
        | Inr h12 ->
          Nf_Inr (w1, False, f0, f1,
            (let annot0 = False in
             let Pair (x, x0) = iHA2 w1 annot0 in
             x (Coq_generic_properties.ret w1 False f1 h12))))), (fun e ->
    match annot with
    | True ->
      Obj.magic (fun w1 incl1 k1 -> Ne_Case (w1, True, f0, f1, Bot,
        (proof_ne_mon w w1 incl1 (Sum (f0, f1)) True e), (Nf_ne ((Cons (f0,
        w1)), True, Bot,
        (let h = let Pair (x, x0) = iHA1 (Cons (f0, w1)) True in x0 in
         Obj.magic h (Ne_Hyp (w1, True, f0)) (Cons (f0, w1))
           (U.wle_refl (Cons (f0, w1))) (fun w2 incl2 h2 ->
           k1 w2
             (U.wle_trans w1 (Cons (f0, w1)) w2 (Prefix_cons (w1, w1, f0,
               (Prefix_refl w1))) incl2) (Inl h2))))), (Nf_ne ((Cons (f1,
        w1)), True, Bot,
        (let h = let Pair (x, x0) = iHA2 (Cons (f1, w1)) True in x0 in
         Obj.magic h (Ne_Hyp (w1, True, f1)) (Cons (f1, w1))
           (U.wle_refl (Cons (f1, w1))) (fun w2 incl2 h2 ->
           k1 w2
             (U.wle_trans w1 (Cons (f1, w1)) w2 (Prefix_cons (w1, w1, f1,
               (Prefix_refl w1))) incl2) (Inr h2)))))))
    | False ->
      Obj.magic (fun c w1 incl1 k1 ->
        match c with
        | Atom a ->
          Ne_Case (w1, False, f0, f1, (Atom a),
            (proof_ne_mon w w1 incl1 (Sum (f0, f1)) False e), (Nf_ne ((Cons
            (f0, w1)), False, (Atom a),
            (let hhypo = Ne_Hyp (w1, False, f0) in
             snd (Obj.magic iHA1 (Cons (f0, w1)) False) hhypo (Atom a) (Cons
               (f0, w1)) (U.wle_refl (Cons (f0, w1))) (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f0, w1)) w2 (Prefix_cons (w1, w1, f0,
                   (Prefix_refl w1))) incl2) (Inl h2))))), (Nf_ne ((Cons (f1,
            w1)), False, (Atom a),
            (let hhypo = Ne_Hyp (w1, False, f1) in
             snd (Obj.magic iHA2 (Cons (f1, w1)) False) hhypo (Atom a) (Cons
               (f1, w1)) (U.wle_refl (Cons (f1, w1))) (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f1, w1)) w2 (Prefix_cons (w1, w1, f1,
                   (Prefix_refl w1))) incl2) (Inr h2))))))
        | Bot ->
          Ne_Case (w1, False, f0, f1, Bot,
            (proof_ne_mon w w1 incl1 (Sum (f0, f1)) False e), (Nf_ne ((Cons
            (f0, w1)), False, Bot,
            (let hhypo = Ne_Hyp (w1, False, f0) in
             snd (Obj.magic iHA1 (Cons (f0, w1)) False) hhypo Bot (Cons (f0,
               w1)) (Prefix_refl (Cons (f0, w1))) (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f0, w1)) w2 (Prefix_cons (w1, w1, f0,
                   (Prefix_refl w1))) incl2) (Inl h2))))), (Nf_ne ((Cons (f1,
            w1)), False, Bot,
            (let hhypo = Ne_Hyp (w1, False, f1) in
             snd (Obj.magic iHA2 (Cons (f1, w1)) False) hhypo Bot (Cons (f1,
               w1)) (U.wle_refl (Cons (f1, w1))) (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f1, w1)) w2 (Prefix_cons (w1, w1, f1,
                   (Prefix_refl w1))) incl2) (Inr h2))))))
        | Func (c1, c2) ->
          Obj.magic (Nf_ne (w1, False, (Func (c1, c2)), (Ne_Case (w1, False,
            f0, f1, (Func (c1, c2)),
            (proof_ne_mon w w1 incl1 (Sum (f0, f1)) False e),
            (let hhypo = Ne_Hyp (w1, False, f0) in
             snd (Obj.magic iHA1 (Cons (f0, w1)) False) hhypo (Func (c1, c2))
               (Cons (f0, w1)) (U.wle_refl (Cons (f0, w1)))
               (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f0, w1)) w2 (Prefix_cons (w1, w1, f0,
                   (Prefix_refl w1))) incl2) (Inl h2))),
            (let hhypo = Ne_Hyp (w1, False, f1) in
             snd (Obj.magic iHA2 (Cons (f1, w1)) False) hhypo (Func (c1, c2))
               (Cons (f1, w1)) (U.wle_refl (Cons (f1, w1)))
               (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f1, w1)) w2 (Prefix_cons (w1, w1, f1,
                   (Prefix_refl w1))) incl2) (Inr h2)))))))
        | Sum (c1, c2) ->
          Obj.magic (Nf_ne (w1, False, (Sum (c1, c2)), (Ne_Case (w1, False,
            f0, f1, (Sum (c1, c2)),
            (proof_ne_mon w w1 incl1 (Sum (f0, f1)) False e),
            (let hhypo = Ne_Hyp (w1, False, f0) in
             snd (Obj.magic iHA1 (Cons (f0, w1)) False) hhypo (Sum (c1, c2))
               (Cons (f0, w1)) (U.wle_refl (Cons (f0, w1)))
               (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f0, w1)) w2 (Prefix_cons (w1, w1, f0,
                   (Prefix_refl w1))) incl2) (Inl h2))),
            (let hhypo = Ne_Hyp (w1, False, f1) in
             snd (Obj.magic iHA2 (Cons (f1, w1)) False) hhypo (Sum (c1, c2))
               (Cons (f1, w1)) (U.wle_refl (Cons (f1, w1)))
               (fun w2 incl2 h2 ->
               k1 w2
                 (U.wle_trans w1 (Cons (f1, w1)) w2 (Prefix_cons (w1, w1, f1,
                   (Prefix_refl w1))) incl2) (Inr h2)))))))))))
  
  module Coq_soundness_for_U = Soundness(U)
  
  (** val coq_Hnil : bool -> unit0 **)
  
  let coq_Hnil annot =
    Tt
  
  (** val coq_NbE : bool -> formula -> proof -> proof_nf **)
  
  let coq_NbE annot a p =
    let compl = fst (completeness a Nil annot) in
    let sndns =
      Coq_soundness_for_U.soundness Nil annot a p Nil annot
        (Obj.magic (coq_Hnil annot))
    in
    compl sndns
 end

