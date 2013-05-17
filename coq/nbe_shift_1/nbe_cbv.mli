type __ = Obj.t

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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

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

val prefix_trans :
  context -> context -> context -> prefix -> prefix -> prefix

val proof_nf_mon :
  context -> context -> prefix -> formula -> bool -> proof_nf -> proof_nf

val proof_ne_mon :
  context -> context -> prefix -> formula -> bool -> proof_ne -> proof_ne

val proof_nf_mon2 :
  formula -> context -> bool -> proof_nf -> bool -> proof_nf

val proof_ne_mon2 :
  formula -> context -> bool -> proof_ne -> bool -> proof_ne

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

module Kripke_structure_monad : 
 functor (Coq_ks:Kripke_structure) ->
 sig 
  type 'f coq_Kont = __
  
  val coq_Kont_mon :
    Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
    Coq_ks.wle -> 'a1 coq_Kont
 end

module Coq_forcing_generic_properties : 
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
 sig 
  module Coq_ks_monad : 
   sig 
    type 'f coq_Kont = __
    
    val coq_Kont_mon :
      Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
      Coq_ks.wle -> 'a1 coq_Kont
   end
  
  val ret :
    Coq_ks.coq_K -> bool -> formula -> Coq_sforces_implementation.sforces ->
    Coq_sforces_implementation.sforces
    Coq_sforces_implementation.Coq_ks_monad.coq_Kont
  
  val bind :
    Coq_ks.coq_K -> bool -> formula -> formula -> (Coq_ks.coq_K -> Coq_ks.wle
    -> Coq_sforces_implementation.sforces ->
    Coq_sforces_implementation.sforces
    Coq_sforces_implementation.Coq_ks_monad.coq_Kont) ->
    Coq_sforces_implementation.sforces
    Coq_sforces_implementation.Coq_ks_monad.coq_Kont ->
    Coq_sforces_implementation.sforces
    Coq_sforces_implementation.Coq_ks_monad.coq_Kont
  
  type sforces_cxt = __
  
  val sforces_cxt_mon :
    context -> Coq_ks.coq_K -> bool -> sforces_cxt -> Coq_ks.coq_K ->
    Coq_ks.wle -> sforces_cxt
  
  val sforces_cxt_mon2 :
    context -> Coq_ks.coq_K -> bool -> sforces_cxt -> bool -> sforces_cxt
  
  type coq_Kont_cxt = __
  
  val coq_Kont_cxt_mon :
    context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> Coq_ks.coq_K ->
    Coq_ks.wle -> coq_Kont_cxt
  
  val coq_Kont_sforces_cxt_mon2 :
    context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> bool -> coq_Kont_cxt
 end

module Coq_sforces_cbv : 
 functor (Coq_ks:Kripke_structure) ->
 sig 
  module Coq_ks_monad : 
   sig 
    type 'f coq_Kont = __
    
    val coq_Kont_mon :
      Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
      Coq_ks.wle -> 'a1 coq_Kont
   end
  
  type sforces = __
  
  val sforces_mon :
    formula -> Coq_ks.coq_K -> bool -> sforces -> Coq_ks.coq_K -> Coq_ks.wle
    -> sforces
  
  val sforces_mon2 : formula -> Coq_ks.coq_K -> sforces -> sforces
  
  val coq_Kont_sforces_mon2 :
    Coq_ks.coq_K -> bool -> formula -> sforces Coq_ks_monad.coq_Kont -> bool
    -> sforces Coq_ks_monad.coq_Kont
  
  val run :
    Coq_ks.coq_K -> bool -> sforces Coq_ks_monad.coq_Kont -> Coq_ks.coq_X
 end

module Soundness : 
 functor (Coq_ks:Kripke_structure) ->
 sig 
  module Coq_ks_monad : 
   sig 
    type 'f coq_Kont = __
    
    val coq_Kont_mon :
      Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
      Coq_ks.wle -> 'a1 coq_Kont
   end
  
  module Coq_cbv_validity : 
   sig 
    module Coq_ks_monad : 
     sig 
      type 'f coq_Kont = __
      
      val coq_Kont_mon :
        Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
        Coq_ks.wle -> 'a1 coq_Kont
     end
    
    type sforces = __
    
    val sforces_mon :
      formula -> Coq_ks.coq_K -> bool -> sforces -> Coq_ks.coq_K ->
      Coq_ks.wle -> sforces
    
    val sforces_mon2 : formula -> Coq_ks.coq_K -> sforces -> sforces
    
    val coq_Kont_sforces_mon2 :
      Coq_ks.coq_K -> bool -> formula -> sforces Coq_ks_monad.coq_Kont ->
      bool -> sforces Coq_ks_monad.coq_Kont
    
    val run :
      Coq_ks.coq_K -> bool -> sforces Coq_ks_monad.coq_Kont -> Coq_ks.coq_X
   end
  
  module Coq_generic_properties : 
   sig 
    module Coq_ks_monad : 
     sig 
      type 'f coq_Kont = __
      
      val coq_Kont_mon :
        Coq_ks.coq_K -> bool -> formula -> 'a1 coq_Kont -> Coq_ks.coq_K ->
        Coq_ks.wle -> 'a1 coq_Kont
     end
    
    val ret :
      Coq_ks.coq_K -> bool -> formula -> Coq_cbv_validity.sforces ->
      Coq_cbv_validity.sforces Coq_cbv_validity.Coq_ks_monad.coq_Kont
    
    val bind :
      Coq_ks.coq_K -> bool -> formula -> formula -> (Coq_ks.coq_K ->
      Coq_ks.wle -> Coq_cbv_validity.sforces -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont) -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont
    
    type sforces_cxt = __
    
    val sforces_cxt_mon :
      context -> Coq_ks.coq_K -> bool -> sforces_cxt -> Coq_ks.coq_K ->
      Coq_ks.wle -> sforces_cxt
    
    val sforces_cxt_mon2 :
      context -> Coq_ks.coq_K -> bool -> sforces_cxt -> bool -> sforces_cxt
    
    type coq_Kont_cxt = __
    
    val coq_Kont_cxt_mon :
      context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> Coq_ks.coq_K ->
      Coq_ks.wle -> coq_Kont_cxt
    
    val coq_Kont_sforces_cxt_mon2 :
      context -> Coq_ks.coq_K -> bool -> coq_Kont_cxt -> bool -> coq_Kont_cxt
   end
  
  val soundness :
    context -> bool -> formula -> proof -> Coq_ks.coq_K -> bool ->
    Coq_generic_properties.sforces_cxt -> Coq_cbv_validity.sforces
    Coq_cbv_validity.Coq_ks_monad.coq_Kont
 end

module Completeness : 
 sig 
  module U : 
   sig 
    type coq_K = context
    
    type wle = prefix
    
    val wle_refl : context -> prefix
    
    val wle_trans :
      context -> context -> context -> prefix -> prefix -> prefix
    
    type coq_X = __
    
    val coq_X_mon :
      context -> bool -> formula -> coq_X -> context -> wle -> coq_X
    
    val coq_X_mon2 : context -> bool -> formula -> coq_X -> bool -> coq_X
    
    val coq_X_reset : context -> bool -> proof_ne -> proof_ne
   end
  
  module Coq_ks_monad : 
   sig 
    type 'f coq_Kont = __
    
    val coq_Kont_mon :
      context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle -> 'a1
      coq_Kont
   end
  
  module Coq_cbv_validity : 
   sig 
    module Coq_ks_monad : 
     sig 
      type 'f coq_Kont = __
      
      val coq_Kont_mon :
        context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle -> 'a1
        coq_Kont
     end
    
    type sforces = __
    
    val sforces_mon :
      formula -> context -> bool -> sforces -> context -> U.wle -> sforces
    
    val sforces_mon2 : formula -> context -> sforces -> sforces
    
    val coq_Kont_sforces_mon2 :
      context -> bool -> formula -> sforces Coq_ks_monad.coq_Kont -> bool ->
      sforces Coq_ks_monad.coq_Kont
    
    val run : context -> bool -> sforces Coq_ks_monad.coq_Kont -> proof_ne
   end
  
  module Coq_generic_properties : 
   sig 
    module Coq_ks_monad : 
     sig 
      type 'f coq_Kont = __
      
      val coq_Kont_mon :
        context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle -> 'a1
        coq_Kont
     end
    
    val ret :
      context -> bool -> formula -> Coq_cbv_validity.sforces ->
      Coq_cbv_validity.sforces Coq_cbv_validity.Coq_ks_monad.coq_Kont
    
    val bind :
      context -> bool -> formula -> formula -> (context -> U.wle ->
      Coq_cbv_validity.sforces -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont) -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont
    
    type sforces_cxt = __
    
    val sforces_cxt_mon :
      context -> context -> bool -> sforces_cxt -> context -> U.wle ->
      sforces_cxt
    
    val sforces_cxt_mon2 :
      context -> context -> bool -> sforces_cxt -> bool -> sforces_cxt
    
    type coq_Kont_cxt = __
    
    val coq_Kont_cxt_mon :
      context -> context -> bool -> coq_Kont_cxt -> context -> U.wle ->
      coq_Kont_cxt
    
    val coq_Kont_sforces_cxt_mon2 :
      context -> context -> bool -> coq_Kont_cxt -> bool -> coq_Kont_cxt
   end
  
  val completeness :
    formula -> context -> bool -> (Coq_cbv_validity.sforces
    Coq_cbv_validity.Coq_ks_monad.coq_Kont -> proof_nf, proof_ne ->
    Coq_cbv_validity.sforces Coq_cbv_validity.Coq_ks_monad.coq_Kont) prod
  
  module Coq_soundness_for_U : 
   sig 
    module Coq_ks_monad : 
     sig 
      type 'f coq_Kont = __
      
      val coq_Kont_mon :
        context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle -> 'a1
        coq_Kont
     end
    
    module Coq_cbv_validity : 
     sig 
      module Coq_ks_monad : 
       sig 
        type 'f coq_Kont = __
        
        val coq_Kont_mon :
          context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle ->
          'a1 coq_Kont
       end
      
      type sforces = __
      
      val sforces_mon :
        formula -> context -> bool -> sforces -> context -> U.wle -> sforces
      
      val sforces_mon2 : formula -> context -> sforces -> sforces
      
      val coq_Kont_sforces_mon2 :
        context -> bool -> formula -> sforces Coq_ks_monad.coq_Kont -> bool
        -> sforces Coq_ks_monad.coq_Kont
      
      val run : context -> bool -> sforces Coq_ks_monad.coq_Kont -> proof_ne
     end
    
    module Coq_generic_properties : 
     sig 
      module Coq_ks_monad : 
       sig 
        type 'f coq_Kont = __
        
        val coq_Kont_mon :
          context -> bool -> formula -> 'a1 coq_Kont -> context -> U.wle ->
          'a1 coq_Kont
       end
      
      val ret :
        context -> bool -> formula -> Coq_cbv_validity.sforces ->
        Coq_cbv_validity.sforces Coq_cbv_validity.Coq_ks_monad.coq_Kont
      
      val bind :
        context -> bool -> formula -> formula -> (context -> U.wle ->
        Coq_cbv_validity.sforces -> Coq_cbv_validity.sforces
        Coq_cbv_validity.Coq_ks_monad.coq_Kont) -> Coq_cbv_validity.sforces
        Coq_cbv_validity.Coq_ks_monad.coq_Kont -> Coq_cbv_validity.sforces
        Coq_cbv_validity.Coq_ks_monad.coq_Kont
      
      type sforces_cxt = __
      
      val sforces_cxt_mon :
        context -> context -> bool -> sforces_cxt -> context -> U.wle ->
        sforces_cxt
      
      val sforces_cxt_mon2 :
        context -> context -> bool -> sforces_cxt -> bool -> sforces_cxt
      
      type coq_Kont_cxt = __
      
      val coq_Kont_cxt_mon :
        context -> context -> bool -> coq_Kont_cxt -> context -> U.wle ->
        coq_Kont_cxt
      
      val coq_Kont_sforces_cxt_mon2 :
        context -> context -> bool -> coq_Kont_cxt -> bool -> coq_Kont_cxt
     end
    
    val soundness :
      context -> bool -> formula -> proof -> context -> bool ->
      Coq_generic_properties.sforces_cxt -> Coq_cbv_validity.sforces
      Coq_cbv_validity.Coq_ks_monad.coq_Kont
   end
  
  val coq_NbE : bool -> formula -> proof -> proof_nf
 end

