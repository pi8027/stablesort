{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module MergesortCoqCbv where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

data Nat =
   O
 | S Nat

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

type Sig2 a = a
  -- singleton inductive, whose constructor was exist2
  
data Reflect =
   ReflectT
 | ReflectF

ssr_have :: a1 -> (a1 -> a2) -> a2
ssr_have step rest =
  rest step

iffP :: Prelude.Bool -> Reflect -> Reflect
iffP _ pb =
  pb

data Alt_spec =
   AltTrue
 | AltFalse

altP :: Prelude.Bool -> Reflect -> Alt_spec
altP _ pb =
  case pb of {
   ReflectT -> AltTrue;
   ReflectF -> AltFalse}

idP :: Prelude.Bool -> Reflect
idP b1 =
  case b1 of {
   Prelude.True -> ReflectT;
   Prelude.False -> ReflectF}

boolP :: Prelude.Bool -> Alt_spec
boolP b1 =
  altP b1 (idP b1)

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

type Axiom t = t -> t -> Reflect

data Mixin_of t =
   Mixin (Rel t) (Axiom t)

op :: (Mixin_of a1) -> Rel a1
op m =
  case m of {
   Mixin op0 _ -> op0}

type Type = Mixin_of Any
  -- singleton inductive, whose constructor was Pack
  
type Sort = Any

class0 :: Type -> Mixin_of Sort
class0 cT =
  cT

eq_op :: Type -> Rel Sort
eq_op t =
  op (class0 t)

eqbP :: Axiom Prelude.Bool
eqbP __top_assumption_ __top_assumption_0 =
  case __top_assumption_ of {
   Prelude.True ->
    case __top_assumption_0 of {
     Prelude.True -> ReflectT;
     Prelude.False -> ReflectF};
   Prelude.False ->
    case __top_assumption_0 of {
     Prelude.True -> ReflectF;
     Prelude.False -> ReflectT}}

bool_eqMixin :: Mixin_of Prelude.Bool
bool_eqMixin =
  Mixin (Prelude.==) eqbP

bool_eqType :: Type
bool_eqType =
  unsafeCoerce bool_eqMixin

eqn :: Nat -> Nat -> Prelude.Bool
eqn m n =
  case m of {
   O -> case n of {
         O -> Prelude.True;
         S _ -> Prelude.False};
   S m' -> case n of {
            O -> Prelude.False;
            S n' -> eqn m' n'}}

eqnP :: Axiom Nat
eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

nat_eqMixin :: Mixin_of Nat
nat_eqMixin =
  Mixin eqn eqnP

nat_eqType :: Type
nat_eqType =
  unsafeCoerce nat_eqMixin

size :: (([]) a1) -> Nat
size s =
  case s of {
   ([]) -> O;
   (:) _ s' -> S (size s')}

nilp :: (([]) a1) -> Prelude.Bool
nilp s =
  eq_op nat_eqType (unsafeCoerce size s) (unsafeCoerce O)

nilP :: (([]) a1) -> Reflect
nilP s =
  case s of {
   ([]) -> ReflectT;
   (:) _ _ -> ReflectF}

cat :: (([]) a1) -> (([]) a1) -> ([]) a1
cat s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) x s1' -> (:) x (cat s1' s2)}

rcons :: (([]) a1) -> a1 -> ([]) a1
rcons s z =
  case s of {
   ([]) -> (:) z ([]);
   (:) x s' -> (:) x (rcons s' z)}

catrev :: (([]) a1) -> (([]) a1) -> ([]) a1
catrev s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) x s1' -> catrev s1' ((:) x s2)}

rev :: (([]) a1) -> ([]) a1
rev s =
  catrev s ([])

foldr :: (a1 -> a2 -> a2) -> a2 -> (([]) a1) -> a2
foldr f z0 s =
  case s of {
   ([]) -> z0;
   (:) x s' -> f x (foldr f z0 s')}

path :: (Rel a1) -> a1 -> (([]) a1) -> Prelude.Bool
path e x p =
  case p of {
   ([]) -> Prelude.True;
   (:) y p' -> andb (e x y) (path e y p')}

sorted :: (Rel a1) -> (([]) a1) -> Prelude.Bool
sorted e s =
  case s of {
   ([]) -> Prelude.True;
   (:) x s' -> path e x s'}

merge :: (Rel a1) -> (([]) a1) -> (([]) a1) -> ([]) a1
merge leT s1 =
  case s1 of {
   ([]) -> (\x -> x);
   (:) x1 s1' ->
    let {
     merge_s1 s2 =
       case s2 of {
        ([]) -> s1;
        (:) x2 s2' ->
         case leT x1 x2 of {
          Prelude.True -> (:) x1 (merge leT s1' s2);
          Prelude.False -> (:) x2 (merge_s1 s2')}}}
    in merge_s1}

data Bool_R =
   Bool_R_true_R
 | Bool_R_false_R

data List_R x0 x a_R =
   List_R_nil_R
 | List_R_cons_R x0 x a_R (([]) x0) (([]) x) (List_R x0 x a_R)

type Pred_R x0 x t_R = x0 -> x -> t_R -> Bool_R

type Rel_R x0 x t_R = x0 -> x -> t_R -> Pred_R x0 x t_R

data Trace t =
   Branch_trace Prelude.Bool (Trace t) (Trace t)
 | Leaf_trace Sort (([]) t)

empty_trace :: (Rel a1) -> Trace a1
empty_trace _ =
  Leaf_trace (unsafeCoerce Prelude.False) ([])

flatten_trace :: (Rel a1) -> (Trace a1) -> ([]) a1
flatten_trace leT t =
  case t of {
   Branch_trace _ l r -> cat (flatten_trace leT l) (flatten_trace leT r);
   Leaf_trace _ s -> s}

sort_trace :: (Rel a1) -> (Trace a1) -> ([]) a1
sort_trace leT t =
  case t of {
   Branch_trace b l r ->
    case b of {
     Prelude.True -> merge leT (sort_trace leT l) (sort_trace leT r);
     Prelude.False ->
      rev
        (merge (\x y -> leT y x) (rev (sort_trace leT r))
          (rev (sort_trace leT l)))};
   Leaf_trace b s ->
    case unsafeCoerce b of {
     Prelude.True -> s;
     Prelude.False -> rev s}}

data Trace_nil_spec t =
   TraceNil
 | TraceNotNil

trace_nilP :: (Rel a1) -> (Trace a1) -> Trace_nil_spec a1
trace_nilP leT t =
  case nilP (sort_trace leT t) of {
   ReflectT ->
    case nilP (flatten_trace leT t) of {
     ReflectT ->
      ssr_have __ (\_ ->
        eq_rec_r ([]) (\_ ->
          ssr_have __ (\_ ->
            eq_rec_r ([]) (\_ -> TraceNil) (sort_trace leT t)))
          (flatten_trace leT t)) __ __;
     ReflectF -> false_rec};
   ReflectF ->
    case nilP (flatten_trace leT t) of {
     ReflectT -> false_rec;
     ReflectF -> TraceNotNil}}

type Sort_ty_R =
  () -> () -> () -> (Rel Any) -> (Rel Any) -> (Rel_R Any Any Any) -> (([])
  Any) -> (([]) Any) -> (List_R Any Any Any) -> List_R Any Any Any

data Function =
   Pack (() -> (Rel Any) -> (([]) Any) -> ([]) Any) Sort_ty_R (() -> (Rel
                                                              Any) -> (([])
                                                              Any) -> Sig2
                                                              (Trace Any))

merge_rec :: (Rel a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> ([]) a1
merge_rec leT xs ys accu =
  case xs of {
   ([]) -> catrev ys accu;
   (:) x xs' ->
    let {
     merge_rec' ys0 accu0 =
       case ys0 of {
        ([]) -> catrev xs accu0;
        (:) y ys' ->
         case leT x y of {
          Prelude.True -> merge_rec leT xs' ys0 ((:) x accu0);
          Prelude.False -> merge_rec' ys' ((:) y accu0)}}}
    in merge_rec' ys accu}

revmerge :: (Rel a1) -> (([]) a1) -> (([]) a1) -> ([]) a1
revmerge leT xs ys =
  merge_rec leT xs ys ([])

revmerge_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([])
              a2) -> (List_R a1 a2 a3) -> (([]) a1) -> (([]) a2) -> (List_R
              a1 a2 a3) -> List_R a1 a2 a3
revmerge_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R =
  let {
   fix_merge_rec_1 = let {
                      merge_rec0 leT xs ys accu =
                        case xs of {
                         ([]) -> catrev ys accu;
                         (:) x xs' ->
                          let {
                           merge_rec' ys0 accu0 =
                             case ys0 of {
                              ([]) -> catrev xs accu0;
                              (:) y ys' ->
                               case leT x y of {
                                Prelude.True ->
                                 merge_rec0 leT xs' ys0 ((:) x accu0);
                                Prelude.False -> merge_rec' ys' ((:) y accu0)}}}
                          in merge_rec' ys accu}}
                     in merge_rec0}
  in
  let {
   fix_merge_rec_2 = let {
                      merge_rec0 leT xs ys accu =
                        case xs of {
                         ([]) -> catrev ys accu;
                         (:) x xs' ->
                          let {
                           merge_rec' ys0 accu0 =
                             case ys0 of {
                              ([]) -> catrev xs accu0;
                              (:) y ys' ->
                               case leT x y of {
                                Prelude.True ->
                                 merge_rec0 leT xs' ys0 ((:) x accu0);
                                Prelude.False -> merge_rec' ys' ((:) y accu0)}}}
                          in merge_rec' ys accu}}
                     in merge_rec0}
  in
  let {
   merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0 xs_UU2081_0 xs_UU2082_0 xs_R0 ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_ accu_UU2082_ accu_R =
     eq_rect
       (case xs_UU2081_0 of {
         ([]) -> catrev ys_UU2081_0 accu_UU2081_;
         (:) x xs' ->
          let {
           merge_rec' ys accu =
             case ys of {
              ([]) -> catrev xs_UU2081_0 accu;
              (:) y ys' ->
               case leT_UU2081_0 x y of {
                Prelude.True ->
                 fix_merge_rec_1 leT_UU2081_0 xs' ys ((:) x accu);
                Prelude.False -> merge_rec' ys' ((:) y accu)}}}
          in merge_rec' ys_UU2081_0 accu_UU2081_})
       (eq_rect
         (case xs_UU2082_0 of {
           ([]) -> catrev ys_UU2082_0 accu_UU2082_;
           (:) x xs' ->
            let {
             merge_rec' ys accu =
               case ys of {
                ([]) -> catrev xs_UU2082_0 accu;
                (:) y ys' ->
                 case leT_UU2082_0 x y of {
                  Prelude.True ->
                   fix_merge_rec_2 leT_UU2082_0 xs' ys ((:) x accu);
                  Prelude.False -> merge_rec' ys' ((:) y accu)}}}
            in merge_rec' ys_UU2082_0 accu_UU2082_})
         (case xs_R0 of {
           List_R_nil_R ->
            let {
             catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
               case s1_R of {
                List_R_nil_R -> s2_R;
                List_R_cons_R x_UU2081_ x_UU2082_ x_R s1'_UU2081_ s1'_UU2082_
                 s1'_R ->
                 catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_
                   s2_UU2081_) ((:) x_UU2082_ s2_UU2082_) (List_R_cons_R
                   x_UU2081_ x_UU2082_ x_R s2_UU2081_ s2_UU2082_ s2_R)}}
            in catrev_R ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_
                 accu_UU2082_ accu_R;
           List_R_cons_R x_UU2081_ x_UU2082_ x_R xs'_UU2081_ xs'_UU2082_
            xs'_R ->
            let {
             fix_merge_rec'_1 = let {
                                 merge_rec' ys accu =
                                   case ys of {
                                    ([]) -> catrev xs_UU2081_0 accu;
                                    (:) y ys' ->
                                     case leT_UU2081_0 x_UU2081_ y of {
                                      Prelude.True ->
                                       fix_merge_rec_1 leT_UU2081_0
                                         xs'_UU2081_ ys ((:) x_UU2081_ accu);
                                      Prelude.False ->
                                       merge_rec' ys' ((:) y accu)}}}
                                in merge_rec'}
            in
            let {
             fix_merge_rec'_2 = let {
                                 merge_rec' ys accu =
                                   case ys of {
                                    ([]) -> catrev xs_UU2082_0 accu;
                                    (:) y ys' ->
                                     case leT_UU2082_0 x_UU2082_ y of {
                                      Prelude.True ->
                                       fix_merge_rec_2 leT_UU2082_0
                                         xs'_UU2082_ ys ((:) x_UU2082_ accu);
                                      Prelude.False ->
                                       merge_rec' ys' ((:) y accu)}}}
                                in merge_rec'}
            in
            let {
             merge_rec'_R ys_UU2081_1 ys_UU2082_1 ys_R1 accu_UU2081_0 accu_UU2082_0 accu_R0 =
               eq_rect
                 (case ys_UU2081_1 of {
                   ([]) -> catrev xs_UU2081_0 accu_UU2081_0;
                   (:) y ys' ->
                    case leT_UU2081_0 x_UU2081_ y of {
                     Prelude.True ->
                      fix_merge_rec_1 leT_UU2081_0 xs'_UU2081_ ys_UU2081_1
                        ((:) x_UU2081_ accu_UU2081_0);
                     Prelude.False ->
                      fix_merge_rec'_1 ys' ((:) y accu_UU2081_0)}})
                 (eq_rect
                   (case ys_UU2082_1 of {
                     ([]) -> catrev xs_UU2082_0 accu_UU2082_0;
                     (:) y ys' ->
                      case leT_UU2082_0 x_UU2082_ y of {
                       Prelude.True ->
                        fix_merge_rec_2 leT_UU2082_0 xs'_UU2082_ ys_UU2082_1
                          ((:) x_UU2082_ accu_UU2082_0);
                       Prelude.False ->
                        fix_merge_rec'_2 ys' ((:) y accu_UU2082_0)}})
                   (case ys_R1 of {
                     List_R_nil_R ->
                      let {
                       catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                         case s1_R of {
                          List_R_nil_R -> s2_R;
                          List_R_cons_R x_UU2081_0 x_UU2082_0 x_R0
                           s1'_UU2081_ s1'_UU2082_ s1'_R ->
                           catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:)
                             x_UU2081_0 s2_UU2081_) ((:) x_UU2082_0
                             s2_UU2082_) (List_R_cons_R x_UU2081_0 x_UU2082_0
                             x_R0 s2_UU2081_ s2_UU2082_ s2_R)}}
                      in catrev_R xs_UU2081_0 xs_UU2082_0 xs_R0 accu_UU2081_0
                           accu_UU2082_0 accu_R0;
                     List_R_cons_R y_UU2081_ y_UU2082_ y_R ys'_UU2081_
                      ys'_UU2082_ ys'_R ->
                      case leT_R0 x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_
                             y_R of {
                       Bool_R_true_R ->
                        merge_rec_R leT_UU2081_0 leT_UU2082_0 leT_R0
                          xs'_UU2081_ xs'_UU2082_ xs'_R ys_UU2081_1
                          ys_UU2082_1 ys_R1 ((:) x_UU2081_ accu_UU2081_0)
                          ((:) x_UU2082_ accu_UU2082_0) (List_R_cons_R
                          x_UU2081_ x_UU2082_ x_R accu_UU2081_0 accu_UU2082_0
                          accu_R0);
                       Bool_R_false_R ->
                        merge_rec'_R ys'_UU2081_ ys'_UU2082_ ys'_R ((:)
                          y_UU2081_ accu_UU2081_0) ((:) y_UU2082_
                          accu_UU2082_0) (List_R_cons_R y_UU2081_ y_UU2082_
                          y_R accu_UU2081_0 accu_UU2082_0 accu_R0)}})
                   (fix_merge_rec'_2 ys_UU2082_1 accu_UU2082_0))
                 (fix_merge_rec'_1 ys_UU2081_1 accu_UU2081_0)}
            in merge_rec'_R ys_UU2081_0 ys_UU2082_0 ys_R0 accu_UU2081_
                 accu_UU2082_ accu_R})
         (fix_merge_rec_2 leT_UU2082_0 xs_UU2082_0 ys_UU2082_0 accu_UU2082_))
       (fix_merge_rec_1 leT_UU2081_0 xs_UU2081_0 ys_UU2081_0 accu_UU2081_)}
  in merge_rec_R leT_UU2081_ leT_UU2082_ leT_R xs_UU2081_ xs_UU2082_ xs_R
       ys_UU2081_ ys_UU2082_ ys_R ([]) ([]) List_R_nil_R

merge_sort_push :: (Rel a1) -> (([]) a1) -> (([]) (([]) a1)) -> ([])
                   (([]) a1)
merge_sort_push leT xs stack =
  case stack of {
   ([]) -> (:) xs stack;
   (:) ys stack0 ->
    case ys of {
     ([]) -> (:) xs stack0;
     (:) _ _ ->
      case stack0 of {
       ([]) -> (:) ([]) ((:) (revmerge leT ys xs) stack0);
       (:) zs stack1 ->
        case zs of {
         ([]) -> (:) ([]) ((:) (revmerge leT ys xs) stack1);
         (:) _ _ -> (:) ([]) ((:) ([])
          (merge_sort_push leT
            (revmerge (\x y -> leT y x) (revmerge leT ys xs) zs) stack1))}}}}

merge_sort_pop :: (Rel a1) -> Prelude.Bool -> (([]) a1) -> (([]) (([]) a1))
                  -> ([]) a1
merge_sort_pop leT mode xs stack =
  case stack of {
   ([]) -> case mode of {
            Prelude.True -> rev xs;
            Prelude.False -> xs};
   (:) ys stack0 ->
    case ys of {
     ([]) ->
      case stack0 of {
       ([]) -> merge_sort_pop leT (Prelude.not mode) (rev xs) stack0;
       (:) l stack1 ->
        case l of {
         ([]) -> merge_sort_pop leT mode xs stack1;
         (:) _ _ -> merge_sort_pop leT (Prelude.not mode) (rev xs) stack0}};
     (:) _ _ ->
      case mode of {
       Prelude.True ->
        merge_sort_pop leT Prelude.False (revmerge (\x y -> leT y x) xs ys)
          stack0;
       Prelude.False ->
        merge_sort_pop leT Prelude.True (revmerge leT ys xs) stack0}}}

sort1rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort1rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT Prelude.False ([]) stack;
   (:) x s0 -> sort1rec leT (merge_sort_push leT ((:) x ([])) stack) s0}

sort1 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort1 leT =
  sort1rec leT ([])

sort2rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort2rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT Prelude.False s stack;
   (:) x1 l ->
    case l of {
     ([]) -> merge_sort_pop leT Prelude.False s stack;
     (:) x2 s' ->
      sort2rec leT
        (merge_sort_push leT
          (case leT x1 x2 of {
            Prelude.True -> (:) x1 ((:) x2 ([]));
            Prelude.False -> (:) x2 ((:) x1 ([]))}) stack) s'}}

sort2 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort2 leT =
  sort2rec leT ([])

sort3rec :: (Rel a1) -> (([]) (([]) a1)) -> (([]) a1) -> ([]) a1
sort3rec leT stack s =
  case s of {
   ([]) -> merge_sort_pop leT Prelude.False s stack;
   (:) x1 l ->
    case l of {
     ([]) -> merge_sort_pop leT Prelude.False s stack;
     (:) x2 l0 ->
      case l0 of {
       ([]) ->
        merge_sort_pop leT Prelude.False
          (case leT x1 x2 of {
            Prelude.True -> s;
            Prelude.False -> (:) x2 ((:) x1 ([]))}) stack;
       (:) x3 s' ->
        sort3rec leT
          (merge_sort_push leT
            (case leT x1 x2 of {
              Prelude.True ->
               case leT x2 x3 of {
                Prelude.True -> (:) x1 ((:) x2 ((:) x3 ([])));
                Prelude.False ->
                 case leT x1 x3 of {
                  Prelude.True -> (:) x1 ((:) x3 ((:) x2 ([])));
                  Prelude.False -> (:) x3 ((:) x1 ((:) x2 ([])))}};
              Prelude.False ->
               case leT x1 x3 of {
                Prelude.True -> (:) x2 ((:) x1 ((:) x3 ([])));
                Prelude.False ->
                 case leT x2 x3 of {
                  Prelude.True -> (:) x2 ((:) x3 ((:) x1 ([])));
                  Prelude.False -> (:) x3 ((:) x2 ((:) x1 ([])))}}}) stack)
          s'}}}

sort3 :: (Rel a1) -> (([]) a1) -> ([]) a1
sort3 leT =
  sort3rec leT ([])

sortNrec :: (Rel a1) -> (([]) (([]) a1)) -> a1 -> (([]) a1) -> ([]) a1
sortNrec leT =
  let {
   sortNrec0 stack x s =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x ([])) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x ([]));
        Prelude.False -> decr0 stack y s0 ((:) x ([]))}};
   incr0 stack x s accu =
     case s of {
      ([]) ->
       merge_sort_pop leT Prelude.False (catrev accu ((:) x ([]))) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x accu);
        Prelude.False ->
         sortNrec0 (merge_sort_push leT (catrev accu ((:) x ([]))) stack) y
           s0}};
   decr0 stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x accu) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True ->
         sortNrec0 (merge_sort_push leT ((:) x accu) stack) y s0;
        Prelude.False -> decr0 stack y s0 ((:) x accu)}}}
  in sortNrec0

incr :: (Rel a1) -> (([]) (([]) a1)) -> a1 -> (([]) a1) -> (([]) a1) -> ([])
        a1
incr leT =
  let {
   sortNrec0 stack x s =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x ([])) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x ([]));
        Prelude.False -> decr0 stack y s0 ((:) x ([]))}};
   incr0 stack x s accu =
     case s of {
      ([]) ->
       merge_sort_pop leT Prelude.False (catrev accu ((:) x ([]))) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x accu);
        Prelude.False ->
         sortNrec0 (merge_sort_push leT (catrev accu ((:) x ([]))) stack) y
           s0}};
   decr0 stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x accu) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True ->
         sortNrec0 (merge_sort_push leT ((:) x accu) stack) y s0;
        Prelude.False -> decr0 stack y s0 ((:) x accu)}}}
  in incr0

decr :: (Rel a1) -> (([]) (([]) a1)) -> a1 -> (([]) a1) -> (([]) a1) -> ([])
        a1
decr leT =
  let {
   sortNrec0 stack x s =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x ([])) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x ([]));
        Prelude.False -> decr0 stack y s0 ((:) x ([]))}};
   incr0 stack x s accu =
     case s of {
      ([]) ->
       merge_sort_pop leT Prelude.False (catrev accu ((:) x ([]))) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr0 stack y s0 ((:) x accu);
        Prelude.False ->
         sortNrec0 (merge_sort_push leT (catrev accu ((:) x ([]))) stack) y
           s0}};
   decr0 stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x accu) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True ->
         sortNrec0 (merge_sort_push leT ((:) x accu) stack) y s0;
        Prelude.False -> decr0 stack y s0 ((:) x accu)}}}
  in decr0

sortN :: (Rel a1) -> (([]) a1) -> ([]) a1
sortN leT s =
  case s of {
   ([]) -> ([]);
   (:) x s0 -> sortNrec leT ([]) x s0}

merge_sort_pushP :: (Rel a1) -> (Trace a1) -> (([]) (Trace a1)) -> Sig2
                    (([]) (Trace a1))
merge_sort_pushP leT =
  let {geT = \x y -> leT y x} in
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:)
                     (case mode of {
                       Prelude.True -> rev (sort_trace leT t);
                       Prelude.False -> sort_trace leT t})
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\t stack ->
  let {
   iHstack t0 __top_assumption_ =
     case __top_assumption_ of {
      ([]) -> (:) t0 ([]);
      (:) a l ->
       case l of {
        ([]) ->
         eq_rect_r (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
           (eq_rect_r
             (case nilp (sort_trace leT a) of {
               Prelude.True -> (:) (sort_trace leT t0) ([]);
               Prelude.False -> (:) ([]) ((:)
                (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                ([]))})
             (eq_rect_r (nilp (flatten_trace leT a))
               (ssr_have (\_ -> nilP) (\__top_assumption_0 ->
                 case __top_assumption_0 __ (flatten_trace leT a) of {
                  ReflectT ->
                   eq_rect_r ([]) ((:) t0 ([])) (flatten_trace leT a);
                  ReflectF -> (:) (empty_trace leT) ((:) (Branch_trace
                   Prelude.True a t0) ([]))})) (nilp (sort_trace leT a)))
             (case sort_trace leT a of {
               ([]) -> (:) (sort_trace leT t0) ([]);
               (:) _ _ -> (:) ([]) ((:)
                (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                ([]))}))
           (revmerge leT (sort_trace leT a) (sort_trace leT t0));
        (:) a0 l0 ->
         eq_rect_r (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
           (eq_rect_r
             (rev
               (merge geT
                 (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                 (rev (sort_trace leT a0))))
             (eq_rect_r
               (case nilp (sort_trace leT a) of {
                 Prelude.True -> (:) (sort_trace leT t0) ((:)
                  (rev (sort_trace leT a0)) (sort_stack Prelude.False l0));
                 Prelude.False ->
                  case rev (sort_trace leT a0) of {
                   ([]) -> (:) ([]) ((:)
                    (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                    (sort_stack Prelude.False l0));
                   (:) _ _ -> (:) ([]) ((:) ([])
                    (merge_sort_push leT
                      (rev
                        (merge geT
                          (rev
                            (merge leT (sort_trace leT a)
                              (sort_trace leT t0)))
                          (rev (sort_trace leT a0))))
                      (sort_stack Prelude.False l0)))}})
               (eq_rect_r
                 (case nilp (rev (sort_trace leT a0)) of {
                   Prelude.True -> (:) ([]) ((:)
                    (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                    (sort_stack Prelude.False l0));
                   Prelude.False -> (:) ([]) ((:) ([])
                    (merge_sort_push leT
                      (rev
                        (merge geT
                          (rev
                            (merge leT (sort_trace leT a)
                              (sort_trace leT t0)))
                          (rev (sort_trace leT a0))))
                      (sort_stack Prelude.False l0)))})
                 (eq_rect_r (nilp (sort_trace leT a0))
                   (eq_rect_r (nilp (flatten_trace leT a))
                     (eq_rect_r (nilp (flatten_trace leT a0))
                       (ssr_have (\_ -> nilP) (\__top_assumption_0 ->
                         case __top_assumption_0 __ (flatten_trace leT a) of {
                          ReflectT ->
                           eq_rect_r ([]) ((:) t0 ((:) a0 l0))
                             (flatten_trace leT a);
                          ReflectF ->
                           eq_rect
                             (cat
                               (cat (flatten_stack l0)
                                 (flatten_trace leT a0))
                               (cat (flatten_trace leT a)
                                 (flatten_trace leT t0)))
                             (eq_rect
                               (cat (flatten_stack l0)
                                 (cat (flatten_trace leT a0)
                                   (cat (flatten_trace leT a)
                                     (flatten_trace leT t0))))
                               (ssr_have (\_ -> nilP) (\__top_assumption_1 ->
                                 case __top_assumption_1 __
                                        (flatten_trace leT a0) of {
                                  ReflectT ->
                                   eq_rect_r ([]) ((:) (empty_trace leT) ((:)
                                     (Branch_trace Prelude.True a t0) l0))
                                     (flatten_trace leT a0);
                                  ReflectF ->
                                   ssr_have
                                     (iHstack (Branch_trace Prelude.False a0
                                       (Branch_trace Prelude.True a t0)) l0)
                                     (\__top_assumption_2 ->
                                     eq_rect_r
                                       (flatten_stack __top_assumption_2)
                                       (\_ ->
                                       eq_rect_r
                                         (sort_stack Prelude.False
                                           __top_assumption_2) ((:)
                                         (empty_trace leT) ((:)
                                         (empty_trace leT)
                                         __top_assumption_2))
                                         (merge_sort_push leT
                                           (rev
                                             (merge geT
                                               (rev
                                                 (merge leT
                                                   (sort_trace leT a)
                                                   (sort_trace leT t0)))
                                               (rev (sort_trace leT a0))))
                                           (sort_stack Prelude.False l0)))
                                       (cat (flatten_stack l0)
                                         (cat (flatten_trace leT a0)
                                           (cat (flatten_trace leT a)
                                             (flatten_trace leT t0)))) __)}))
                               (cat
                                 (cat (flatten_stack l0)
                                   (flatten_trace leT a0))
                                 (cat (flatten_trace leT a)
                                   (flatten_trace leT t0))))
                             (cat
                               (cat
                                 (cat (flatten_stack l0)
                                   (flatten_trace leT a0))
                                 (flatten_trace leT a))
                               (flatten_trace leT t0))}))
                       (nilp (sort_trace leT a0))) (nilp (sort_trace leT a)))
                   (nilp (rev (sort_trace leT a0))))
                 (case rev (sort_trace leT a0) of {
                   ([]) -> (:) ([]) ((:)
                    (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                    (sort_stack Prelude.False l0));
                   (:) _ _ -> (:) ([]) ((:) ([])
                    (merge_sort_push leT
                      (rev
                        (merge geT
                          (rev
                            (merge leT (sort_trace leT a)
                              (sort_trace leT t0)))
                          (rev (sort_trace leT a0))))
                      (sort_stack Prelude.False l0)))}))
               (case sort_trace leT a of {
                 ([]) -> (:) (sort_trace leT t0) ((:)
                  (rev (sort_trace leT a0)) (sort_stack Prelude.False l0));
                 (:) _ _ ->
                  case rev (sort_trace leT a0) of {
                   ([]) -> (:) ([]) ((:)
                    (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
                    (sort_stack Prelude.False l0));
                   (:) _ _ -> (:) ([]) ((:) ([])
                    (merge_sort_push leT
                      (rev
                        (merge geT
                          (rev
                            (merge leT (sort_trace leT a)
                              (sort_trace leT t0)))
                          (rev (sort_trace leT a0))))
                      (sort_stack Prelude.False l0)))}}))
             (revmerge geT
               (rev (merge leT (sort_trace leT a) (sort_trace leT t0)))
               (rev (sort_trace leT a0))))
           (revmerge leT (sort_trace leT a) (sort_trace leT t0))}}}
  in iHstack t stack)

merge_sort_popP :: (Rel a1) -> Prelude.Bool -> (Trace a1) -> (([])
                   (Trace a1)) -> Sig2 (Trace a1)
merge_sort_popP leT =
  let {geT = \x y -> leT y x} in
  let {
   condrev = \r s -> case r of {
                      Prelude.True -> rev s;
                      Prelude.False -> s}}
  in
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:) (condrev mode (sort_trace leT t))
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\mode t stack ->
  let {
   iHstack mode0 t0 __top_assumption_ =
     case __top_assumption_ of {
      ([]) -> t0;
      (:) a l ->
       eq_rect
         (cat (flatten_stack l)
           (cat (flatten_trace leT a) (flatten_trace leT t0)))
         (eq_rect_r
           (rev
             (merge geT (condrev mode0 (sort_trace leT t0))
               (condrev mode0 (sort_trace leT a))))
           (eq_rect_r
             (rev
               (merge leT (condrev mode0 (sort_trace leT a))
                 (condrev mode0 (sort_trace leT t0))))
             (eq_rect_r
               (case nilp (condrev mode0 (sort_trace leT a)) of {
                 Prelude.True ->
                  case sort_stack (Prelude.not mode0) l of {
                   ([]) ->
                    merge_sort_pop leT (Prelude.not mode0)
                      (rev (condrev mode0 (sort_trace leT t0)))
                      (sort_stack (Prelude.not mode0) l);
                   (:) l0 stack0 ->
                    case l0 of {
                     ([]) ->
                      merge_sort_pop leT mode0
                        (condrev mode0 (sort_trace leT t0)) stack0;
                     (:) _ _ ->
                      merge_sort_pop leT (Prelude.not mode0)
                        (rev (condrev mode0 (sort_trace leT t0)))
                        (sort_stack (Prelude.not mode0) l)}};
                 Prelude.False ->
                  case mode0 of {
                   Prelude.True ->
                    merge_sort_pop leT Prelude.False
                      (rev
                        (merge geT (condrev mode0 (sort_trace leT t0))
                          (condrev mode0 (sort_trace leT a))))
                      (sort_stack (Prelude.not mode0) l);
                   Prelude.False ->
                    merge_sort_pop leT Prelude.True
                      (rev
                        (merge leT (condrev mode0 (sort_trace leT a))
                          (condrev mode0 (sort_trace leT t0))))
                      (sort_stack (Prelude.not mode0) l)}})
               (eq_rect_r (nilp (sort_trace leT a))
                 (case trace_nilP leT a of {
                   TraceNil ->
                    case l of {
                     ([]) -> t0;
                     (:) a0 l0 ->
                      eq_rect_r
                        (rev
                          (merge geT
                            (rev (condrev mode0 (sort_trace leT t0)))
                            (condrev (Prelude.not mode0) (sort_trace leT a0))))
                        (eq_rect_r
                          (rev
                            (merge leT
                              (condrev (Prelude.not mode0)
                                (sort_trace leT a0))
                              (rev (condrev mode0 (sort_trace leT t0)))))
                          (eq_rect_r
                            (case nilp
                                    (condrev (Prelude.not mode0)
                                      (sort_trace leT a0)) of {
                              Prelude.True ->
                               merge_sort_pop leT mode0
                                 (condrev mode0 (sort_trace leT t0))
                                 (sort_stack
                                   (Prelude.not (Prelude.not mode0)) l0);
                              Prelude.False ->
                               case condrev (Prelude.not mode0)
                                      (sort_trace leT a0) of {
                                ([]) ->
                                 case sort_stack
                                        (Prelude.not (Prelude.not mode0)) l0 of {
                                  ([]) ->
                                   merge_sort_pop leT
                                     (Prelude.not (Prelude.not mode0))
                                     (rev
                                       (rev
                                         (condrev mode0 (sort_trace leT t0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  (:) l1 stack0 ->
                                   case l1 of {
                                    ([]) ->
                                     merge_sort_pop leT (Prelude.not mode0)
                                       (rev
                                         (condrev mode0 (sort_trace leT t0)))
                                       stack0;
                                    (:) _ _ ->
                                     merge_sort_pop leT
                                       (Prelude.not (Prelude.not mode0))
                                       (rev
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0))))
                                       (sort_stack
                                         (Prelude.not (Prelude.not mode0))
                                         l0)}};
                                (:) _ _ ->
                                 case Prelude.not mode0 of {
                                  Prelude.True ->
                                   merge_sort_pop leT Prelude.False
                                     (rev
                                       (merge geT
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  Prelude.False ->
                                   merge_sort_pop leT Prelude.True
                                     (rev
                                       (merge leT
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0)}}})
                            (eq_rect_r
                              (case nilp
                                      (condrev (Prelude.not mode0)
                                        (sort_trace leT a0)) of {
                                Prelude.True ->
                                 case sort_stack
                                        (Prelude.not (Prelude.not mode0)) l0 of {
                                  ([]) ->
                                   merge_sort_pop leT
                                     (Prelude.not (Prelude.not mode0))
                                     (rev
                                       (rev
                                         (condrev mode0 (sort_trace leT t0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  (:) l1 stack0 ->
                                   case l1 of {
                                    ([]) ->
                                     merge_sort_pop leT (Prelude.not mode0)
                                       (rev
                                         (condrev mode0 (sort_trace leT t0)))
                                       stack0;
                                    (:) _ _ ->
                                     merge_sort_pop leT
                                       (Prelude.not (Prelude.not mode0))
                                       (rev
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0))))
                                       (sort_stack
                                         (Prelude.not (Prelude.not mode0))
                                         l0)}};
                                Prelude.False ->
                                 case Prelude.not mode0 of {
                                  Prelude.True ->
                                   merge_sort_pop leT Prelude.False
                                     (rev
                                       (merge geT
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  Prelude.False ->
                                   merge_sort_pop leT Prelude.True
                                     (rev
                                       (merge leT
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0)}})
                              (eq_rect_r (nilp (sort_trace leT a0))
                                (eq_rect_r mode0
                                  (eq_rect_r
                                    (condrev mode0 (sort_trace leT t0))
                                    (case trace_nilP leT a0 of {
                                      TraceNil ->
                                       eq_rect_r (flatten_stack l0)
                                         (iHstack mode0 t0 l0)
                                         (cat (flatten_stack l0) ([]));
                                      TraceNotNil ->
                                       eq_rect
                                         (cat (flatten_stack l0)
                                           (cat (flatten_trace leT a0)
                                             (flatten_trace leT t0)))
                                         (case mode0 of {
                                           Prelude.True ->
                                            eq_rect_r (sort_trace leT t0)
                                              (\iHstack0 -> iHstack0)
                                              (rev (rev (sort_trace leT t0)))
                                              (iHstack mode0 (Branch_trace
                                                mode0 a0 t0) l0);
                                           Prelude.False ->
                                            iHstack mode0 (Branch_trace mode0
                                              a0 t0) l0})
                                         (cat
                                           (cat (flatten_stack l0)
                                             (flatten_trace leT a0))
                                           (flatten_trace leT t0))})
                                    (rev
                                      (rev
                                        (condrev mode0 (sort_trace leT t0)))))
                                  (Prelude.not (Prelude.not mode0)))
                                (nilp
                                  (condrev (Prelude.not mode0)
                                    (sort_trace leT a0))))
                              (case condrev (Prelude.not mode0)
                                      (sort_trace leT a0) of {
                                ([]) ->
                                 case sort_stack
                                        (Prelude.not (Prelude.not mode0)) l0 of {
                                  ([]) ->
                                   merge_sort_pop leT
                                     (Prelude.not (Prelude.not mode0))
                                     (rev
                                       (rev
                                         (condrev mode0 (sort_trace leT t0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  (:) l1 stack0 ->
                                   case l1 of {
                                    ([]) ->
                                     merge_sort_pop leT (Prelude.not mode0)
                                       (rev
                                         (condrev mode0 (sort_trace leT t0)))
                                       stack0;
                                    (:) _ _ ->
                                     merge_sort_pop leT
                                       (Prelude.not (Prelude.not mode0))
                                       (rev
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0))))
                                       (sort_stack
                                         (Prelude.not (Prelude.not mode0))
                                         l0)}};
                                (:) _ _ ->
                                 case Prelude.not mode0 of {
                                  Prelude.True ->
                                   merge_sort_pop leT Prelude.False
                                     (rev
                                       (merge geT
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  Prelude.False ->
                                   merge_sort_pop leT Prelude.True
                                     (rev
                                       (merge leT
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0)}}))
                            (case condrev (Prelude.not mode0)
                                    (sort_trace leT a0) of {
                              ([]) ->
                               merge_sort_pop leT mode0
                                 (condrev mode0 (sort_trace leT t0))
                                 (sort_stack
                                   (Prelude.not (Prelude.not mode0)) l0);
                              (:) _ _ ->
                               case condrev (Prelude.not mode0)
                                      (sort_trace leT a0) of {
                                ([]) ->
                                 case sort_stack
                                        (Prelude.not (Prelude.not mode0)) l0 of {
                                  ([]) ->
                                   merge_sort_pop leT
                                     (Prelude.not (Prelude.not mode0))
                                     (rev
                                       (rev
                                         (condrev mode0 (sort_trace leT t0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  (:) l1 stack0 ->
                                   case l1 of {
                                    ([]) ->
                                     merge_sort_pop leT (Prelude.not mode0)
                                       (rev
                                         (condrev mode0 (sort_trace leT t0)))
                                       stack0;
                                    (:) _ _ ->
                                     merge_sort_pop leT
                                       (Prelude.not (Prelude.not mode0))
                                       (rev
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0))))
                                       (sort_stack
                                         (Prelude.not (Prelude.not mode0))
                                         l0)}};
                                (:) _ _ ->
                                 case Prelude.not mode0 of {
                                  Prelude.True ->
                                   merge_sort_pop leT Prelude.False
                                     (rev
                                       (merge geT
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0);
                                  Prelude.False ->
                                   merge_sort_pop leT Prelude.True
                                     (rev
                                       (merge leT
                                         (condrev (Prelude.not mode0)
                                           (sort_trace leT a0))
                                         (rev
                                           (condrev mode0
                                             (sort_trace leT t0)))))
                                     (sort_stack
                                       (Prelude.not (Prelude.not mode0)) l0)}}}))
                          (revmerge leT
                            (condrev (Prelude.not mode0) (sort_trace leT a0))
                            (rev (condrev mode0 (sort_trace leT t0)))))
                        (revmerge geT
                          (rev (condrev mode0 (sort_trace leT t0)))
                          (condrev (Prelude.not mode0) (sort_trace leT a0)))};
                   TraceNotNil ->
                    iHstack (Prelude.not mode0) (Branch_trace
                      (Prelude.not mode0) a t0) l})
                 (nilp (condrev mode0 (sort_trace leT a))))
               (case condrev mode0 (sort_trace leT a) of {
                 ([]) ->
                  case sort_stack (Prelude.not mode0) l of {
                   ([]) ->
                    merge_sort_pop leT (Prelude.not mode0)
                      (rev (condrev mode0 (sort_trace leT t0)))
                      (sort_stack (Prelude.not mode0) l);
                   (:) l0 stack0 ->
                    case l0 of {
                     ([]) ->
                      merge_sort_pop leT mode0
                        (condrev mode0 (sort_trace leT t0)) stack0;
                     (:) _ _ ->
                      merge_sort_pop leT (Prelude.not mode0)
                        (rev (condrev mode0 (sort_trace leT t0)))
                        (sort_stack (Prelude.not mode0) l)}};
                 (:) _ _ ->
                  case mode0 of {
                   Prelude.True ->
                    merge_sort_pop leT Prelude.False
                      (rev
                        (merge geT (condrev mode0 (sort_trace leT t0))
                          (condrev mode0 (sort_trace leT a))))
                      (sort_stack (Prelude.not mode0) l);
                   Prelude.False ->
                    merge_sort_pop leT Prelude.True
                      (rev
                        (merge leT (condrev mode0 (sort_trace leT a))
                          (condrev mode0 (sort_trace leT t0))))
                      (sort_stack (Prelude.not mode0) l)}}))
             (revmerge leT (condrev mode0 (sort_trace leT a))
               (condrev mode0 (sort_trace leT t0))))
           (revmerge geT (condrev mode0 (sort_trace leT t0))
             (condrev mode0 (sort_trace leT a))))
         (cat (cat (flatten_stack l) (flatten_trace leT a))
           (flatten_trace leT t0))}}
  in iHstack mode t stack)

sort1P :: (Rel a1) -> (([]) a1) -> Sig2 (Trace a1)
sort1P leT =
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:)
                     (case mode of {
                       Prelude.True -> rev (sort_trace leT t);
                       Prelude.False -> sort_trace leT t})
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\s ->
  ssr_have __ (\_ ->
    eq_rect_r (cat (flatten_stack ([])) s)
      (ssr_have __ (\_ ->
        eq_rect_r (sort_stack Prelude.False ([]))
          (list_rect (\stack ->
            merge_sort_popP leT Prelude.False (empty_trace leT) stack)
            (\x s0 iHs stack ->
            eq_rect_r (cat (cat (flatten_stack stack) ((:) x ([]))) s0)
              (\stack0 _ ->
              eq_rect_r (flatten_stack stack0) (\_ ->
                eq_rect_r (sort_stack Prelude.False stack0) (iHs stack0)
                  (merge_sort_push leT ((:) x ([]))
                    (sort_stack Prelude.False stack)))
                (cat (flatten_stack stack) ((:) x ([]))))
              (cat (flatten_stack stack) ((:) x s0))
              (merge_sort_pushP leT (Leaf_trace (unsafeCoerce Prelude.True)
                ((:) x ([]))) stack) __ __) s ([])) ([]))) s))

sort2P :: (Rel a1) -> (([]) a1) -> Sig2 (Trace a1)
sort2P leT =
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:)
                     (case mode of {
                       Prelude.True -> rev (sort_trace leT t);
                       Prelude.False -> sort_trace leT t})
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\s ->
  ssr_have __ (\_ ->
    eq_rect_r (cat (flatten_stack ([])) s)
      (ssr_have __ (\_ ->
        eq_rect_r (sort_stack Prelude.False ([]))
          (let {
            iHs stack __top_assumption_ =
              case __top_assumption_ of {
               ([]) ->
                merge_sort_popP leT Prelude.False (Leaf_trace
                  (unsafeCoerce Prelude.True) ([])) stack;
               (:) a l ->
                case l of {
                 ([]) ->
                  merge_sort_popP leT Prelude.False (Leaf_trace
                    (unsafeCoerce Prelude.True) ((:) a ([]))) stack;
                 (:) a0 l0 ->
                  eq_rect_r
                    (cat (cat (flatten_stack stack) ((:) a ((:) a0 ([]))))
                      l0) (\_ stack0 _ ->
                    eq_rect_r (flatten_stack stack0) (\_ ->
                      eq_rect_r (sort_stack Prelude.False stack0)
                        (iHs stack0 l0)
                        (merge_sort_push leT
                          (case leT a a0 of {
                            Prelude.True -> (:) a ((:) a0 ([]));
                            Prelude.False -> (:) a0 ((:) a ([]))})
                          (sort_stack Prelude.False stack)))
                      (cat (flatten_stack stack) ((:) a ((:) a0 ([])))))
                    (cat (flatten_stack stack) ((:) a ((:) a0 l0))) __
                    (merge_sort_pushP leT (Leaf_trace (unsafeCoerce leT a a0)
                      ((:) a ((:) a0 ([])))) stack) __ __}}}
           in iHs ([]) s) ([]))) s))

sort3P :: (Rel a1) -> (([]) a1) -> Sig2 (Trace a1)
sort3P leT =
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:)
                     (case mode of {
                       Prelude.True -> rev (sort_trace leT t);
                       Prelude.False -> sort_trace leT t})
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\s ->
  ssr_have __ (\_ ->
    ssr_have __ (\_ ->
      eq_rect_r (cat (flatten_stack ([])) s)
        (ssr_have __ (\_ ->
          eq_rect_r (sort_stack Prelude.False ([]))
            (let {
              iHs stack __top_assumption_ =
                case __top_assumption_ of {
                 ([]) ->
                  merge_sort_popP leT Prelude.False (Leaf_trace
                    (unsafeCoerce Prelude.True) ([])) stack;
                 (:) a l ->
                  case l of {
                   ([]) ->
                    merge_sort_popP leT Prelude.False (Leaf_trace
                      (unsafeCoerce Prelude.True) ((:) a ([]))) stack;
                   (:) a0 l0 ->
                    case l0 of {
                     ([]) ->
                      merge_sort_popP leT Prelude.False (Leaf_trace
                        (unsafeCoerce leT a a0) ((:) a ((:) a0 ([])))) stack;
                     (:) a1 l1 ->
                      eq_rect_r
                        (cat
                          (cat (flatten_stack stack) ((:) a ((:) a0 ((:) a1
                            ([]))))) l1)
                        (let {
                          stack' = merge_sort_pushP leT (Branch_trace
                                     Prelude.False (Leaf_trace
                                     (unsafeCoerce leT a a0) ((:) a ((:) a0
                                     ([])))) (Leaf_trace
                                     (unsafeCoerce Prelude.True) ((:) a1
                                     ([])))) stack}
                         in
                         eq_rect_r (flatten_stack stack')
                           (let {
                             push2 = merge_sort_push leT
                                       (case leT a a0 of {
                                         Prelude.True ->
                                          case leT a0 a1 of {
                                           Prelude.True -> (:) a ((:) a0 ((:)
                                            a1 ([])));
                                           Prelude.False ->
                                            case leT a a1 of {
                                             Prelude.True -> (:) a ((:) a1
                                              ((:) a0 ([])));
                                             Prelude.False -> (:) a1 ((:) a
                                              ((:) a0 ([])))}};
                                         Prelude.False ->
                                          case leT a a1 of {
                                           Prelude.True -> (:) a0 ((:) a ((:)
                                            a1 ([])));
                                           Prelude.False ->
                                            case leT a0 a1 of {
                                             Prelude.True -> (:) a0 ((:) a1
                                              ((:) a ([])));
                                             Prelude.False -> (:) a1 ((:) a0
                                              ((:) a ([])))}}})
                                       (sort_stack Prelude.False stack)}
                            in
                            ssr_have __ (\_ ->
                              eq_rect_r push2 (\_ ->
                                eq_rect_r (sort_stack Prelude.False stack')
                                  (iHs stack' l1) push2)
                                (merge_sort_push leT
                                  (rev
                                    (merge (\x y -> leT y x)
                                      (rev ((:) a1 ([])))
                                      (rev
                                        (case leT a a0 of {
                                          Prelude.True -> (:) a ((:) a0 ([]));
                                          Prelude.False ->
                                           rev ((:) a ((:) a0 ([])))}))))
                                  (sort_stack Prelude.False stack))))
                           (cat (flatten_stack stack) ((:) a ((:) a0 ((:) a1
                             ([]))))) __)
                        (cat (flatten_stack stack) ((:) a ((:) a0 ((:) a1
                          l1))))}}}}
             in iHs ([]) s) ([]))) s)))

sortNP :: (Rel a1) -> (([]) a1) -> Sig2 (Trace a1)
sortNP leT =
  let {flatten_stack = foldr (\x x0 -> cat x0 (flatten_trace leT x)) ([])} in
  let {
   sort_stack = let {
                 sort_stack mode stack =
                   case stack of {
                    ([]) -> ([]);
                    (:) t stack0 -> (:)
                     (case mode of {
                       Prelude.True -> rev (sort_trace leT t);
                       Prelude.False -> sort_trace leT t})
                     (sort_stack (Prelude.not mode) stack0)}}
                in sort_stack}
  in
  (\s ->
  case s of {
   ([]) -> empty_trace leT;
   (:) a l ->
    ssr_have __ (\_ ->
      eq_rect_r (cat (flatten_stack ([])) ((:) a l))
        (ssr_have __ (\_ ->
          eq_rect_r (sort_stack Prelude.False ([]))
            (let {
              iHs stack x __top_assumption_ =
                case __top_assumption_ of {
                 ([]) ->
                  merge_sort_popP leT Prelude.False (Leaf_trace
                    (unsafeCoerce Prelude.True) ((:) x ([]))) stack;
                 (:) a0 l0 ->
                  ssr_have __
                    (ssr_have __ (\_ ->
                      eq_rect_r (cat (rev ((:) a0 ((:) x ([])))) l0)
                        (list_rect (\ord x0 acc ->
                          eq_rect
                            (sorted (\x1 z ->
                              eq_op bool_eqType (unsafeCoerce leT x1 z)
                                (unsafeCoerce ord)) (rev ((:) x0 acc)))
                            (eq_rect_r (rev ((:) x0 acc)) (\_ ->
                              let {
                               t = merge_sort_popP leT Prelude.False
                                     (Leaf_trace (unsafeCoerce ord)
                                     (rev ((:) x0 acc))) stack}
                              in
                              eq_rect_r (flatten_trace leT t)
                                (eq_rect_r ((:) x0 acc) (\_ ->
                                  case ord of {
                                   Prelude.True ->
                                    eq_rect_r (sort_trace leT t) t
                                      (merge_sort_pop leT Prelude.False
                                        (catrev acc ((:) x0 ([])))
                                        (sort_stack Prelude.False stack));
                                   Prelude.False ->
                                    eq_rect_r (sort_trace leT t) t
                                      (merge_sort_pop leT Prelude.False ((:)
                                        x0 acc)
                                        (sort_stack Prelude.False stack))})
                                  (rev (rev ((:) x0 acc))))
                                (cat (flatten_stack stack)
                                  (rev ((:) x0 acc))) __)
                              (cat (rev ((:) x0 acc)) ([])))
                            (sorted (\y x1 ->
                              eq_op bool_eqType (unsafeCoerce leT x1 y)
                                (unsafeCoerce ord)) ((:) x0 acc)))
                          (\y s0 iHs' ord x0 acc ->
                          case ord of {
                           Prelude.True ->
                            case boolP (leT x0 y) of {
                             AltTrue -> (\_ ->
                              ssr_have __ (\_ ->
                                let {t = iHs' Prelude.True y ((:) x0 acc) __}
                                in
                                eq_rect (cat (rcons (rev ((:) x0 acc)) y) s0)
                                  (eq_rect (rev ((:) y ((:) x0 acc))) (\_ ->
                                    eq_rect_r (flatten_trace leT t) (\_ ->
                                      eq_rect_r (sort_trace leT t) t
                                        (incr leT
                                          (sort_stack Prelude.False stack) y
                                          s0 ((:) x0 acc)))
                                      (cat (flatten_stack stack)
                                        (cat (rev ((:) y ((:) x0 acc))) s0)))
                                    (rcons (rev ((:) x0 acc)) y))
                                  (cat (rev ((:) x0 acc)) ((:) y s0)) __ __));
                             AltFalse ->
                              eq_rect
                                (sorted (\x1 z ->
                                  eq_op bool_eqType (unsafeCoerce leT x1 z)
                                    (unsafeCoerce Prelude.True))
                                  (rev ((:) x0 acc))) (\_ ->
                                let {
                                 stack' = merge_sort_pushP leT (Leaf_trace
                                            (unsafeCoerce Prelude.True)
                                            (rev ((:) x0 acc))) stack}
                                in
                                eq_rect_r
                                  (cat
                                    (cat (flatten_stack stack)
                                      (rev ((:) x0 acc))) ((:) y s0)) (\_ ->
                                  eq_rect_r (flatten_stack stack') (\_ ->
                                    eq_rect_r
                                      (sort_stack Prelude.False stack')
                                      (iHs stack' y s0)
                                      (merge_sort_push leT
                                        (catrev acc ((:) x0 ([])))
                                        (sort_stack Prelude.False stack)))
                                    (cat (flatten_stack stack)
                                      (rev ((:) x0 acc))))
                                  (cat (flatten_stack stack)
                                    (cat (rev ((:) x0 acc)) ((:) y s0))) __
                                  __)
                                (sorted (\y0 x1 ->
                                  eq_op bool_eqType (unsafeCoerce leT x1 y0)
                                    (unsafeCoerce Prelude.True)) ((:) x0
                                  acc))};
                           Prelude.False ->
                            case boolP (leT x0 y) of {
                             AltTrue ->
                              eq_rect
                                (sorted (\x1 z ->
                                  eq_op bool_eqType (unsafeCoerce leT x1 z)
                                    (unsafeCoerce Prelude.False))
                                  (rev ((:) x0 acc))) (\_ ->
                                let {
                                 stack' = merge_sort_pushP leT (Leaf_trace
                                            (unsafeCoerce Prelude.False)
                                            (rev ((:) x0 acc))) stack}
                                in
                                eq_rect_r
                                  (cat
                                    (cat (flatten_stack stack)
                                      (rev ((:) x0 acc))) ((:) y s0))
                                  (eq_rect_r ((:) x0 acc) (\_ ->
                                    eq_rect_r (flatten_stack stack') (\_ ->
                                      eq_rect_r
                                        (sort_stack Prelude.False stack')
                                        (iHs stack' y s0)
                                        (merge_sort_push leT ((:) x0 acc)
                                          (sort_stack Prelude.False stack)))
                                      (cat (flatten_stack stack)
                                        (rev ((:) x0 acc))))
                                    (rev (rev ((:) x0 acc))))
                                  (cat (flatten_stack stack)
                                    (cat (rev ((:) x0 acc)) ((:) y s0))) __
                                  __)
                                (sorted (\y0 x1 ->
                                  eq_op bool_eqType (unsafeCoerce leT x1 y0)
                                    (unsafeCoerce Prelude.False)) ((:) x0
                                  acc));
                             AltFalse -> (\_ ->
                              ssr_have __ (\_ ->
                                let {
                                 t = iHs' Prelude.False y ((:) x0 acc) __}
                                in
                                eq_rect (cat (rcons (rev ((:) x0 acc)) y) s0)
                                  (eq_rect (rev ((:) y ((:) x0 acc))) (\_ ->
                                    eq_rect_r (flatten_trace leT t) (\_ ->
                                      eq_rect_r (sort_trace leT t) t
                                        (decr leT
                                          (sort_stack Prelude.False stack) y
                                          s0 ((:) x0 acc)))
                                      (cat (flatten_stack stack)
                                        (cat (rev ((:) y ((:) x0 acc))) s0)))
                                    (rcons (rev ((:) x0 acc)) y))
                                  (cat (rev ((:) x0 acc)) ((:) y s0)) __ __))}})
                          l0 (leT x a0) a0 ((:) x ([]))) ((:) x ((:) a0 l0))))}}
             in iHs ([]) a l) ([]))) ((:) a l))})

revmerge_R0 :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([])
               a2) -> (List_R a1 a2 a3) -> (([]) a1) -> (([]) a2) -> (List_R
               a1 a2 a3) -> List_R a1 a2 a3
revmerge_R0 =
  revmerge_R

merge_sort_push_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) 
                     a1) -> (([]) a2) -> (List_R a1 a2 a3) -> (([])
                     (([]) a1)) -> (([]) (([]) a2)) -> (List_R (([]) a1)
                     (([]) a2) (List_R a1 a2 a3)) -> List_R (([]) a1)
                     (([]) a2) (List_R a1 a2 a3)
merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R =
  let {geT_UU2081_ = \x y -> leT_UU2081_ y x} in
  let {geT_UU2082_ = \x y -> leT_UU2082_ y x} in
  let {
   fix_merge_sort_push_1 = let {
                            merge_sort_push0 xs stack =
                              case stack of {
                               ([]) -> (:) xs stack;
                               (:) ys stack0 ->
                                case ys of {
                                 ([]) -> (:) xs stack0;
                                 (:) _ _ ->
                                  case stack0 of {
                                   ([]) -> (:) ([]) ((:)
                                    (revmerge leT_UU2081_ ys xs) stack0);
                                   (:) zs stack1 ->
                                    case zs of {
                                     ([]) -> (:) ([]) ((:)
                                      (revmerge leT_UU2081_ ys xs) stack1);
                                     (:) _ _ -> (:) ([]) ((:) ([])
                                      (merge_sort_push0
                                        (revmerge geT_UU2081_
                                          (revmerge leT_UU2081_ ys xs) zs)
                                        stack1))}}}}}
                           in merge_sort_push0}
  in
  let {
   fix_merge_sort_push_2 = let {
                            merge_sort_push0 xs stack =
                              case stack of {
                               ([]) -> (:) xs stack;
                               (:) ys stack0 ->
                                case ys of {
                                 ([]) -> (:) xs stack0;
                                 (:) _ _ ->
                                  case stack0 of {
                                   ([]) -> (:) ([]) ((:)
                                    (revmerge leT_UU2082_ ys xs) stack0);
                                   (:) zs stack1 ->
                                    case zs of {
                                     ([]) -> (:) ([]) ((:)
                                      (revmerge leT_UU2082_ ys xs) stack1);
                                     (:) _ _ -> (:) ([]) ((:) ([])
                                      (merge_sort_push0
                                        (revmerge geT_UU2082_
                                          (revmerge leT_UU2082_ ys xs) zs)
                                        stack1))}}}}}
                           in merge_sort_push0}
  in
  let {
   merge_sort_push_R0 xs_UU2081_ xs_UU2082_ xs_R stack_UU2081_ stack_UU2082_ stack_R =
     eq_rect
       (case stack_UU2081_ of {
         ([]) -> (:) xs_UU2081_ stack_UU2081_;
         (:) ys stack ->
          case ys of {
           ([]) -> (:) xs_UU2081_ stack;
           (:) _ _ ->
            case stack of {
             ([]) -> (:) ([]) ((:) (revmerge leT_UU2081_ ys xs_UU2081_)
              stack);
             (:) zs stack0 ->
              case zs of {
               ([]) -> (:) ([]) ((:) (revmerge leT_UU2081_ ys xs_UU2081_)
                stack0);
               (:) _ _ -> (:) ([]) ((:) ([])
                (fix_merge_sort_push_1
                  (revmerge geT_UU2081_ (revmerge leT_UU2081_ ys xs_UU2081_)
                    zs) stack0))}}}})
       (eq_rect
         (case stack_UU2082_ of {
           ([]) -> (:) xs_UU2082_ stack_UU2082_;
           (:) ys stack ->
            case ys of {
             ([]) -> (:) xs_UU2082_ stack;
             (:) _ _ ->
              case stack of {
               ([]) -> (:) ([]) ((:) (revmerge leT_UU2082_ ys xs_UU2082_)
                stack);
               (:) zs stack0 ->
                case zs of {
                 ([]) -> (:) ([]) ((:) (revmerge leT_UU2082_ ys xs_UU2082_)
                  stack0);
                 (:) _ _ -> (:) ([]) ((:) ([])
                  (fix_merge_sort_push_2
                    (revmerge geT_UU2082_
                      (revmerge leT_UU2082_ ys xs_UU2082_) zs) stack0))}}}})
         (case stack_R of {
           List_R_nil_R -> List_R_cons_R xs_UU2081_ xs_UU2082_ xs_R
            stack_UU2081_ stack_UU2082_ stack_R;
           List_R_cons_R ys_UU2081_ ys_UU2082_ ys_R stack_UU2081_0
            stack_UU2082_0 stack_R0 ->
            case ys_R of {
             List_R_nil_R -> List_R_cons_R xs_UU2081_ xs_UU2082_ xs_R
              stack_UU2081_0 stack_UU2082_0 stack_R0;
             List_R_cons_R _ _ _ _ _ _ ->
              case stack_R0 of {
               List_R_nil_R -> List_R_cons_R ([]) ([]) List_R_nil_R ((:)
                (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_) stack_UU2081_0)
                ((:) (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                stack_UU2082_0) (List_R_cons_R
                (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                (revmerge_R0 leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_
                  ys_UU2082_ ys_R xs_UU2081_ xs_UU2082_ xs_R) stack_UU2081_0
                stack_UU2082_0 stack_R0);
               List_R_cons_R zs_UU2081_ zs_UU2082_ zs_R stack_UU2081_1
                stack_UU2082_1 stack_R1 ->
                case zs_R of {
                 List_R_nil_R -> List_R_cons_R ([]) ([]) List_R_nil_R ((:)
                  (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                  stack_UU2081_1) ((:)
                  (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                  stack_UU2082_1) (List_R_cons_R
                  (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                  (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                  (revmerge_R0 leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_
                    ys_UU2082_ ys_R xs_UU2081_ xs_UU2082_ xs_R)
                  stack_UU2081_1 stack_UU2082_1 stack_R1);
                 List_R_cons_R _ _ _ _ _ _ -> List_R_cons_R ([]) ([])
                  List_R_nil_R ((:) ([])
                  (fix_merge_sort_push_1
                    (revmerge geT_UU2081_
                      (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                      zs_UU2081_) stack_UU2081_1)) ((:) ([])
                  (fix_merge_sort_push_2
                    (revmerge geT_UU2082_
                      (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                      zs_UU2082_) stack_UU2082_1)) (List_R_cons_R ([]) ([])
                  List_R_nil_R
                  (fix_merge_sort_push_1
                    (revmerge geT_UU2081_
                      (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                      zs_UU2081_) stack_UU2081_1)
                  (fix_merge_sort_push_2
                    (revmerge geT_UU2082_
                      (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                      zs_UU2082_) stack_UU2082_1)
                  (merge_sort_push_R0
                    (revmerge geT_UU2081_
                      (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                      zs_UU2081_)
                    (revmerge geT_UU2082_
                      (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                      zs_UU2082_)
                    (revmerge_R0 geT_UU2081_ geT_UU2082_
                      (\x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R ->
                      leT_R y_UU2081_ y_UU2082_ y_R x_UU2081_ x_UU2082_ x_R)
                      (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
                      (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
                      (revmerge_R0 leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_
                        ys_UU2082_ ys_R xs_UU2081_ xs_UU2082_ xs_R)
                      zs_UU2081_ zs_UU2082_ zs_R) stack_UU2081_1
                    stack_UU2082_1 stack_R1))}}}})
         (fix_merge_sort_push_2 xs_UU2082_ stack_UU2082_))
       (fix_merge_sort_push_1 xs_UU2081_ stack_UU2081_)}
  in merge_sort_push_R0

merge_sort_pop_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> Prelude.Bool
                    -> Prelude.Bool -> Bool_R -> (([]) a1) -> (([]) a2) ->
                    (List_R a1 a2 a3) -> (([]) (([]) a1)) -> (([]) (([]) a2))
                    -> (List_R (([]) a1) (([]) a2) (List_R a1 a2 a3)) ->
                    List_R a1 a2 a3
merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R =
  let {geT_UU2081_ = \x y -> leT_UU2081_ y x} in
  let {geT_UU2082_ = \x y -> leT_UU2082_ y x} in
  let {
   merge_sort_pop_R0 mode_UU2081_ mode_UU2082_ mode_R xs_UU2081_ xs_UU2082_ xs_R _ _ stack_R =
     case stack_R of {
      List_R_nil_R ->
       case mode_R of {
        Bool_R_true_R ->
         let {
          catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
            case s1_R of {
             List_R_nil_R -> s2_R;
             List_R_cons_R x_UU2081_ x_UU2082_ x_R s1'_UU2081_ s1'_UU2082_
              s1'_R ->
              catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_
                s2_UU2081_) ((:) x_UU2082_ s2_UU2082_) (List_R_cons_R
                x_UU2081_ x_UU2082_ x_R s2_UU2081_ s2_UU2082_ s2_R)}}
         in catrev_R xs_UU2081_ xs_UU2082_ xs_R ([]) ([]) List_R_nil_R;
        Bool_R_false_R -> xs_R};
      List_R_cons_R ys_UU2081_ ys_UU2082_ ys_R stack_UU2081_ stack_UU2082_
       stack_R0 ->
       case ys_R of {
        List_R_nil_R ->
         case stack_R0 of {
          List_R_nil_R ->
           merge_sort_pop_R0 (Prelude.not mode_UU2081_)
             (Prelude.not mode_UU2082_)
             (case mode_R of {
               Bool_R_true_R -> Bool_R_false_R;
               Bool_R_false_R -> Bool_R_true_R}) (rev xs_UU2081_)
             (rev xs_UU2082_)
             (let {
               catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                 case s1_R of {
                  List_R_nil_R -> s2_R;
                  List_R_cons_R x_UU2081_ x_UU2082_ x_R s1'_UU2081_
                   s1'_UU2082_ s1'_R ->
                   catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_
                     s2_UU2081_) ((:) x_UU2082_ s2_UU2082_) (List_R_cons_R
                     x_UU2081_ x_UU2082_ x_R s2_UU2081_ s2_UU2082_ s2_R)}}
              in catrev_R xs_UU2081_ xs_UU2082_ xs_R ([]) ([]) List_R_nil_R)
             stack_UU2081_ stack_UU2082_ stack_R0;
          List_R_cons_R _ _ l_R stack_UU2081_0 stack_UU2082_0 stack_R1 ->
           case l_R of {
            List_R_nil_R ->
             merge_sort_pop_R0 mode_UU2081_ mode_UU2082_ mode_R xs_UU2081_
               xs_UU2082_ xs_R stack_UU2081_0 stack_UU2082_0 stack_R1;
            List_R_cons_R _ _ _ _ _ _ ->
             merge_sort_pop_R0 (Prelude.not mode_UU2081_)
               (Prelude.not mode_UU2082_)
               (case mode_R of {
                 Bool_R_true_R -> Bool_R_false_R;
                 Bool_R_false_R -> Bool_R_true_R}) (rev xs_UU2081_)
               (rev xs_UU2082_)
               (let {
                 catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                   case s1_R of {
                    List_R_nil_R -> s2_R;
                    List_R_cons_R x_UU2081_ x_UU2082_ x_R s1'_UU2081_
                     s1'_UU2082_ s1'_R ->
                     catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_
                       s2_UU2081_) ((:) x_UU2082_ s2_UU2082_) (List_R_cons_R
                       x_UU2081_ x_UU2082_ x_R s2_UU2081_ s2_UU2082_ s2_R)}}
                in catrev_R xs_UU2081_ xs_UU2082_ xs_R ([]) ([]) List_R_nil_R)
               stack_UU2081_ stack_UU2082_ stack_R0}};
        List_R_cons_R _ _ _ _ _ _ ->
         case mode_R of {
          Bool_R_true_R ->
           merge_sort_pop_R0 Prelude.False Prelude.False Bool_R_false_R
             (revmerge geT_UU2081_ xs_UU2081_ ys_UU2081_)
             (revmerge geT_UU2082_ xs_UU2082_ ys_UU2082_)
             (revmerge_R0 geT_UU2081_ geT_UU2082_
               (\x_UU2081_ x_UU2082_ x_R y_UU2081_ y_UU2082_ y_R ->
               leT_R y_UU2081_ y_UU2082_ y_R x_UU2081_ x_UU2082_ x_R)
               xs_UU2081_ xs_UU2082_ xs_R ys_UU2081_ ys_UU2082_ ys_R)
             stack_UU2081_ stack_UU2082_ stack_R0;
          Bool_R_false_R ->
           merge_sort_pop_R0 Prelude.True Prelude.True Bool_R_true_R
             (revmerge leT_UU2081_ ys_UU2081_ xs_UU2081_)
             (revmerge leT_UU2082_ ys_UU2082_ xs_UU2082_)
             (revmerge_R0 leT_UU2081_ leT_UU2082_ leT_R ys_UU2081_ ys_UU2082_
               ys_R xs_UU2081_ xs_UU2082_ xs_R) stack_UU2081_ stack_UU2082_
             stack_R0}}}}
  in merge_sort_pop_R0

sort1_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([]) 
           a2) -> (List_R a1 a2 a3) -> List_R a1 a2 a3
sort1_R leT_UU2081_ leT_UU2082_ leT_R =
  let {
   sort1rec_R stack_UU2081_ stack_UU2082_ stack_R _ _ s_R =
     case s_R of {
      List_R_nil_R ->
       merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
         Prelude.False Bool_R_false_R ([]) ([]) List_R_nil_R stack_UU2081_
         stack_UU2082_ stack_R;
      List_R_cons_R x_UU2081_ x_UU2082_ x_R s_UU2081_ s_UU2082_ s_R0 ->
       sort1rec_R
         (merge_sort_push leT_UU2081_ ((:) x_UU2081_ ([])) stack_UU2081_)
         (merge_sort_push leT_UU2082_ ((:) x_UU2082_ ([])) stack_UU2082_)
         (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R ((:) x_UU2081_
           ([])) ((:) x_UU2082_ ([])) (List_R_cons_R x_UU2081_ x_UU2082_ x_R
           ([]) ([]) List_R_nil_R) stack_UU2081_ stack_UU2082_ stack_R)
         s_UU2081_ s_UU2082_ s_R0}}
  in sort1rec_R ([]) ([]) List_R_nil_R

sort2_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([]) 
           a2) -> (List_R a1 a2 a3) -> List_R a1 a2 a3
sort2_R leT_UU2081_ leT_UU2082_ leT_R =
  let {
   fix_sort2rec_1 = let {
                     sort2rec0 stack s =
                       case s of {
                        ([]) ->
                         merge_sort_pop leT_UU2081_ Prelude.False s stack;
                        (:) x1 l ->
                         case l of {
                          ([]) ->
                           merge_sort_pop leT_UU2081_ Prelude.False s stack;
                          (:) x2 s' ->
                           sort2rec0
                             (merge_sort_push leT_UU2081_
                               (case leT_UU2081_ x1 x2 of {
                                 Prelude.True -> (:) x1 ((:) x2 ([]));
                                 Prelude.False -> (:) x2 ((:) x1 ([]))})
                               stack) s'}}}
                    in sort2rec0}
  in
  let {
   fix_sort2rec_2 = let {
                     sort2rec0 stack s =
                       case s of {
                        ([]) ->
                         merge_sort_pop leT_UU2082_ Prelude.False s stack;
                        (:) x1 l ->
                         case l of {
                          ([]) ->
                           merge_sort_pop leT_UU2082_ Prelude.False s stack;
                          (:) x2 s' ->
                           sort2rec0
                             (merge_sort_push leT_UU2082_
                               (case leT_UU2082_ x1 x2 of {
                                 Prelude.True -> (:) x1 ((:) x2 ([]));
                                 Prelude.False -> (:) x2 ((:) x1 ([]))})
                               stack) s'}}}
                    in sort2rec0}
  in
  let {
   sort2rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R =
     eq_rect
       (case s_UU2081_ of {
         ([]) ->
          merge_sort_pop leT_UU2081_ Prelude.False s_UU2081_ stack_UU2081_;
         (:) x1 l ->
          case l of {
           ([]) ->
            merge_sort_pop leT_UU2081_ Prelude.False s_UU2081_ stack_UU2081_;
           (:) x2 s' ->
            fix_sort2rec_1
              (merge_sort_push leT_UU2081_
                (case leT_UU2081_ x1 x2 of {
                  Prelude.True -> (:) x1 ((:) x2 ([]));
                  Prelude.False -> (:) x2 ((:) x1 ([]))}) stack_UU2081_) s'}})
       (eq_rect
         (case s_UU2082_ of {
           ([]) ->
            merge_sort_pop leT_UU2082_ Prelude.False s_UU2082_ stack_UU2082_;
           (:) x1 l ->
            case l of {
             ([]) ->
              merge_sort_pop leT_UU2082_ Prelude.False s_UU2082_
                stack_UU2082_;
             (:) x2 s' ->
              fix_sort2rec_2
                (merge_sort_push leT_UU2082_
                  (case leT_UU2082_ x1 x2 of {
                    Prelude.True -> (:) x1 ((:) x2 ([]));
                    Prelude.False -> (:) x2 ((:) x1 ([]))}) stack_UU2082_) s'}})
         (case s_R of {
           List_R_nil_R ->
            merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
              Prelude.False Bool_R_false_R s_UU2081_ s_UU2082_ s_R
              stack_UU2081_ stack_UU2082_ stack_R;
           List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R _ _ l_R ->
            case l_R of {
             List_R_nil_R ->
              merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
                Prelude.False Bool_R_false_R s_UU2081_ s_UU2082_ s_R
                stack_UU2081_ stack_UU2082_ stack_R;
             List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R s'_UU2081_ s'_UU2082_
              s'_R ->
              let {
               s1_UU2081_ = case leT_UU2081_ x1_UU2081_ x2_UU2081_ of {
                             Prelude.True -> (:) x1_UU2081_ ((:) x2_UU2081_
                              ([]));
                             Prelude.False -> (:) x2_UU2081_ ((:) x1_UU2081_
                              ([]))}}
              in
              let {
               s1_UU2082_ = case leT_UU2082_ x1_UU2082_ x2_UU2082_ of {
                             Prelude.True -> (:) x1_UU2082_ ((:) x2_UU2082_
                              ([]));
                             Prelude.False -> (:) x2_UU2082_ ((:) x1_UU2082_
                              ([]))}}
              in
              sort2rec_R
                (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
                (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
                (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
                  s1_UU2082_
                  (case leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_
                          x2_UU2082_ x2_R of {
                    Bool_R_true_R -> List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R
                     ((:) x2_UU2081_ ([])) ((:) x2_UU2082_ ([]))
                     (List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R ([]) ([])
                     List_R_nil_R);
                    Bool_R_false_R -> List_R_cons_R x2_UU2081_ x2_UU2082_
                     x2_R ((:) x1_UU2081_ ([])) ((:) x1_UU2082_ ([]))
                     (List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R ([]) ([])
                     List_R_nil_R)}) stack_UU2081_ stack_UU2082_ stack_R)
                s'_UU2081_ s'_UU2082_ s'_R}})
         (fix_sort2rec_2 stack_UU2082_ s_UU2082_))
       (fix_sort2rec_1 stack_UU2081_ s_UU2081_)}
  in sort2rec_R ([]) ([]) List_R_nil_R

sort3_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([]) 
           a2) -> (List_R a1 a2 a3) -> List_R a1 a2 a3
sort3_R leT_UU2081_ leT_UU2082_ leT_R =
  let {
   fix_sort3rec_1 = let {
                     sort3rec0 stack s =
                       case s of {
                        ([]) ->
                         merge_sort_pop leT_UU2081_ Prelude.False s stack;
                        (:) x1 l ->
                         case l of {
                          ([]) ->
                           merge_sort_pop leT_UU2081_ Prelude.False s stack;
                          (:) x2 l0 ->
                           case l0 of {
                            ([]) ->
                             merge_sort_pop leT_UU2081_ Prelude.False
                               (case leT_UU2081_ x1 x2 of {
                                 Prelude.True -> s;
                                 Prelude.False -> (:) x2 ((:) x1 ([]))})
                               stack;
                            (:) x3 s' ->
                             sort3rec0
                               (merge_sort_push leT_UU2081_
                                 (case leT_UU2081_ x1 x2 of {
                                   Prelude.True ->
                                    case leT_UU2081_ x2 x3 of {
                                     Prelude.True -> (:) x1 ((:) x2 ((:) x3
                                      ([])));
                                     Prelude.False ->
                                      case leT_UU2081_ x1 x3 of {
                                       Prelude.True -> (:) x1 ((:) x3 ((:) x2
                                        ([])));
                                       Prelude.False -> (:) x3 ((:) x1 ((:)
                                        x2 ([])))}};
                                   Prelude.False ->
                                    case leT_UU2081_ x1 x3 of {
                                     Prelude.True -> (:) x2 ((:) x1 ((:) x3
                                      ([])));
                                     Prelude.False ->
                                      case leT_UU2081_ x2 x3 of {
                                       Prelude.True -> (:) x2 ((:) x3 ((:) x1
                                        ([])));
                                       Prelude.False -> (:) x3 ((:) x2 ((:)
                                        x1 ([])))}}}) stack) s'}}}}
                    in sort3rec0}
  in
  let {
   fix_sort3rec_2 = let {
                     sort3rec0 stack s =
                       case s of {
                        ([]) ->
                         merge_sort_pop leT_UU2082_ Prelude.False s stack;
                        (:) x1 l ->
                         case l of {
                          ([]) ->
                           merge_sort_pop leT_UU2082_ Prelude.False s stack;
                          (:) x2 l0 ->
                           case l0 of {
                            ([]) ->
                             merge_sort_pop leT_UU2082_ Prelude.False
                               (case leT_UU2082_ x1 x2 of {
                                 Prelude.True -> s;
                                 Prelude.False -> (:) x2 ((:) x1 ([]))})
                               stack;
                            (:) x3 s' ->
                             sort3rec0
                               (merge_sort_push leT_UU2082_
                                 (case leT_UU2082_ x1 x2 of {
                                   Prelude.True ->
                                    case leT_UU2082_ x2 x3 of {
                                     Prelude.True -> (:) x1 ((:) x2 ((:) x3
                                      ([])));
                                     Prelude.False ->
                                      case leT_UU2082_ x1 x3 of {
                                       Prelude.True -> (:) x1 ((:) x3 ((:) x2
                                        ([])));
                                       Prelude.False -> (:) x3 ((:) x1 ((:)
                                        x2 ([])))}};
                                   Prelude.False ->
                                    case leT_UU2082_ x1 x3 of {
                                     Prelude.True -> (:) x2 ((:) x1 ((:) x3
                                      ([])));
                                     Prelude.False ->
                                      case leT_UU2082_ x2 x3 of {
                                       Prelude.True -> (:) x2 ((:) x3 ((:) x1
                                        ([])));
                                       Prelude.False -> (:) x3 ((:) x2 ((:)
                                        x1 ([])))}}}) stack) s'}}}}
                    in sort3rec0}
  in
  let {
   sort3rec_R stack_UU2081_ stack_UU2082_ stack_R s_UU2081_ s_UU2082_ s_R =
     eq_rect
       (case s_UU2081_ of {
         ([]) ->
          merge_sort_pop leT_UU2081_ Prelude.False s_UU2081_ stack_UU2081_;
         (:) x1 l ->
          case l of {
           ([]) ->
            merge_sort_pop leT_UU2081_ Prelude.False s_UU2081_ stack_UU2081_;
           (:) x2 l0 ->
            case l0 of {
             ([]) ->
              merge_sort_pop leT_UU2081_ Prelude.False
                (case leT_UU2081_ x1 x2 of {
                  Prelude.True -> s_UU2081_;
                  Prelude.False -> (:) x2 ((:) x1 ([]))}) stack_UU2081_;
             (:) x3 s' ->
              fix_sort3rec_1
                (merge_sort_push leT_UU2081_
                  (case leT_UU2081_ x1 x2 of {
                    Prelude.True ->
                     case leT_UU2081_ x2 x3 of {
                      Prelude.True -> (:) x1 ((:) x2 ((:) x3 ([])));
                      Prelude.False ->
                       case leT_UU2081_ x1 x3 of {
                        Prelude.True -> (:) x1 ((:) x3 ((:) x2 ([])));
                        Prelude.False -> (:) x3 ((:) x1 ((:) x2 ([])))}};
                    Prelude.False ->
                     case leT_UU2081_ x1 x3 of {
                      Prelude.True -> (:) x2 ((:) x1 ((:) x3 ([])));
                      Prelude.False ->
                       case leT_UU2081_ x2 x3 of {
                        Prelude.True -> (:) x2 ((:) x3 ((:) x1 ([])));
                        Prelude.False -> (:) x3 ((:) x2 ((:) x1 ([])))}}})
                  stack_UU2081_) s'}}})
       (eq_rect
         (case s_UU2082_ of {
           ([]) ->
            merge_sort_pop leT_UU2082_ Prelude.False s_UU2082_ stack_UU2082_;
           (:) x1 l ->
            case l of {
             ([]) ->
              merge_sort_pop leT_UU2082_ Prelude.False s_UU2082_
                stack_UU2082_;
             (:) x2 l0 ->
              case l0 of {
               ([]) ->
                merge_sort_pop leT_UU2082_ Prelude.False
                  (case leT_UU2082_ x1 x2 of {
                    Prelude.True -> s_UU2082_;
                    Prelude.False -> (:) x2 ((:) x1 ([]))}) stack_UU2082_;
               (:) x3 s' ->
                fix_sort3rec_2
                  (merge_sort_push leT_UU2082_
                    (case leT_UU2082_ x1 x2 of {
                      Prelude.True ->
                       case leT_UU2082_ x2 x3 of {
                        Prelude.True -> (:) x1 ((:) x2 ((:) x3 ([])));
                        Prelude.False ->
                         case leT_UU2082_ x1 x3 of {
                          Prelude.True -> (:) x1 ((:) x3 ((:) x2 ([])));
                          Prelude.False -> (:) x3 ((:) x1 ((:) x2 ([])))}};
                      Prelude.False ->
                       case leT_UU2082_ x1 x3 of {
                        Prelude.True -> (:) x2 ((:) x1 ((:) x3 ([])));
                        Prelude.False ->
                         case leT_UU2082_ x2 x3 of {
                          Prelude.True -> (:) x2 ((:) x3 ((:) x1 ([])));
                          Prelude.False -> (:) x3 ((:) x2 ((:) x1 ([])))}}})
                    stack_UU2082_) s'}}})
         (case s_R of {
           List_R_nil_R ->
            merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
              Prelude.False Bool_R_false_R s_UU2081_ s_UU2082_ s_R
              stack_UU2081_ stack_UU2082_ stack_R;
           List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R _ _ l_R ->
            case l_R of {
             List_R_nil_R ->
              merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
                Prelude.False Bool_R_false_R s_UU2081_ s_UU2082_ s_R
                stack_UU2081_ stack_UU2082_ stack_R;
             List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R _ _ l0_R ->
              case l0_R of {
               List_R_nil_R ->
                merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
                  Prelude.False Bool_R_false_R
                  (case leT_UU2081_ x1_UU2081_ x2_UU2081_ of {
                    Prelude.True -> s_UU2081_;
                    Prelude.False -> (:) x2_UU2081_ ((:) x1_UU2081_ ([]))})
                  (case leT_UU2082_ x1_UU2082_ x2_UU2082_ of {
                    Prelude.True -> s_UU2082_;
                    Prelude.False -> (:) x2_UU2082_ ((:) x1_UU2082_ ([]))})
                  (case leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_
                          x2_UU2082_ x2_R of {
                    Bool_R_true_R -> s_R;
                    Bool_R_false_R -> List_R_cons_R x2_UU2081_ x2_UU2082_
                     x2_R ((:) x1_UU2081_ ([])) ((:) x1_UU2082_ ([]))
                     (List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R ([]) ([])
                     List_R_nil_R)}) stack_UU2081_ stack_UU2082_ stack_R;
               List_R_cons_R x3_UU2081_ x3_UU2082_ x3_R s'_UU2081_ s'_UU2082_
                s'_R ->
                let {
                 s1_UU2081_ = case leT_UU2081_ x1_UU2081_ x2_UU2081_ of {
                               Prelude.True ->
                                case leT_UU2081_ x2_UU2081_ x3_UU2081_ of {
                                 Prelude.True -> (:) x1_UU2081_ ((:)
                                  x2_UU2081_ ((:) x3_UU2081_ ([])));
                                 Prelude.False ->
                                  case leT_UU2081_ x1_UU2081_ x3_UU2081_ of {
                                   Prelude.True -> (:) x1_UU2081_ ((:)
                                    x3_UU2081_ ((:) x2_UU2081_ ([])));
                                   Prelude.False -> (:) x3_UU2081_ ((:)
                                    x1_UU2081_ ((:) x2_UU2081_ ([])))}};
                               Prelude.False ->
                                case leT_UU2081_ x1_UU2081_ x3_UU2081_ of {
                                 Prelude.True -> (:) x2_UU2081_ ((:)
                                  x1_UU2081_ ((:) x3_UU2081_ ([])));
                                 Prelude.False ->
                                  case leT_UU2081_ x2_UU2081_ x3_UU2081_ of {
                                   Prelude.True -> (:) x2_UU2081_ ((:)
                                    x3_UU2081_ ((:) x1_UU2081_ ([])));
                                   Prelude.False -> (:) x3_UU2081_ ((:)
                                    x2_UU2081_ ((:) x1_UU2081_ ([])))}}}}
                in
                let {
                 s1_UU2082_ = case leT_UU2082_ x1_UU2082_ x2_UU2082_ of {
                               Prelude.True ->
                                case leT_UU2082_ x2_UU2082_ x3_UU2082_ of {
                                 Prelude.True -> (:) x1_UU2082_ ((:)
                                  x2_UU2082_ ((:) x3_UU2082_ ([])));
                                 Prelude.False ->
                                  case leT_UU2082_ x1_UU2082_ x3_UU2082_ of {
                                   Prelude.True -> (:) x1_UU2082_ ((:)
                                    x3_UU2082_ ((:) x2_UU2082_ ([])));
                                   Prelude.False -> (:) x3_UU2082_ ((:)
                                    x1_UU2082_ ((:) x2_UU2082_ ([])))}};
                               Prelude.False ->
                                case leT_UU2082_ x1_UU2082_ x3_UU2082_ of {
                                 Prelude.True -> (:) x2_UU2082_ ((:)
                                  x1_UU2082_ ((:) x3_UU2082_ ([])));
                                 Prelude.False ->
                                  case leT_UU2082_ x2_UU2082_ x3_UU2082_ of {
                                   Prelude.True -> (:) x2_UU2082_ ((:)
                                    x3_UU2082_ ((:) x1_UU2082_ ([])));
                                   Prelude.False -> (:) x3_UU2082_ ((:)
                                    x2_UU2082_ ((:) x1_UU2082_ ([])))}}}}
                in
                sort3rec_R
                  (merge_sort_push leT_UU2081_ s1_UU2081_ stack_UU2081_)
                  (merge_sort_push leT_UU2082_ s1_UU2082_ stack_UU2082_)
                  (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R s1_UU2081_
                    s1_UU2082_
                    (case leT_R x1_UU2081_ x1_UU2082_ x1_R x2_UU2081_
                            x2_UU2082_ x2_R of {
                      Bool_R_true_R ->
                       case leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                              x3_UU2082_ x3_R of {
                        Bool_R_true_R -> List_R_cons_R x1_UU2081_ x1_UU2082_
                         x1_R ((:) x2_UU2081_ ((:) x3_UU2081_ ([]))) ((:)
                         x2_UU2082_ ((:) x3_UU2082_ ([]))) (List_R_cons_R
                         x2_UU2081_ x2_UU2082_ x2_R ((:) x3_UU2081_ ([]))
                         ((:) x3_UU2082_ ([])) (List_R_cons_R x3_UU2081_
                         x3_UU2082_ x3_R ([]) ([]) List_R_nil_R));
                        Bool_R_false_R ->
                         case leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                                x3_UU2082_ x3_R of {
                          Bool_R_true_R -> List_R_cons_R x1_UU2081_
                           x1_UU2082_ x1_R ((:) x3_UU2081_ ((:) x2_UU2081_
                           ([]))) ((:) x3_UU2082_ ((:) x2_UU2082_ ([])))
                           (List_R_cons_R x3_UU2081_ x3_UU2082_ x3_R ((:)
                           x2_UU2081_ ([])) ((:) x2_UU2082_ ([]))
                           (List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R ([])
                           ([]) List_R_nil_R));
                          Bool_R_false_R -> List_R_cons_R x3_UU2081_
                           x3_UU2082_ x3_R ((:) x1_UU2081_ ((:) x2_UU2081_
                           ([]))) ((:) x1_UU2082_ ((:) x2_UU2082_ ([])))
                           (List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R ((:)
                           x2_UU2081_ ([])) ((:) x2_UU2082_ ([]))
                           (List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R ([])
                           ([]) List_R_nil_R))}};
                      Bool_R_false_R ->
                       case leT_R x1_UU2081_ x1_UU2082_ x1_R x3_UU2081_
                              x3_UU2082_ x3_R of {
                        Bool_R_true_R -> List_R_cons_R x2_UU2081_ x2_UU2082_
                         x2_R ((:) x1_UU2081_ ((:) x3_UU2081_ ([]))) ((:)
                         x1_UU2082_ ((:) x3_UU2082_ ([]))) (List_R_cons_R
                         x1_UU2081_ x1_UU2082_ x1_R ((:) x3_UU2081_ ([]))
                         ((:) x3_UU2082_ ([])) (List_R_cons_R x3_UU2081_
                         x3_UU2082_ x3_R ([]) ([]) List_R_nil_R));
                        Bool_R_false_R ->
                         case leT_R x2_UU2081_ x2_UU2082_ x2_R x3_UU2081_
                                x3_UU2082_ x3_R of {
                          Bool_R_true_R -> List_R_cons_R x2_UU2081_
                           x2_UU2082_ x2_R ((:) x3_UU2081_ ((:) x1_UU2081_
                           ([]))) ((:) x3_UU2082_ ((:) x1_UU2082_ ([])))
                           (List_R_cons_R x3_UU2081_ x3_UU2082_ x3_R ((:)
                           x1_UU2081_ ([])) ((:) x1_UU2082_ ([]))
                           (List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R ([])
                           ([]) List_R_nil_R));
                          Bool_R_false_R -> List_R_cons_R x3_UU2081_
                           x3_UU2082_ x3_R ((:) x2_UU2081_ ((:) x1_UU2081_
                           ([]))) ((:) x2_UU2082_ ((:) x1_UU2082_ ([])))
                           (List_R_cons_R x2_UU2081_ x2_UU2082_ x2_R ((:)
                           x1_UU2081_ ([])) ((:) x1_UU2082_ ([]))
                           (List_R_cons_R x1_UU2081_ x1_UU2082_ x1_R ([])
                           ([]) List_R_nil_R))}}}) stack_UU2081_
                    stack_UU2082_ stack_R) s'_UU2081_ s'_UU2082_ s'_R}}})
         (fix_sort3rec_2 stack_UU2082_ s_UU2082_))
       (fix_sort3rec_1 stack_UU2081_ s_UU2081_)}
  in sort3rec_R ([]) ([]) List_R_nil_R

sortN_R :: (Rel a1) -> (Rel a2) -> (Rel_R a1 a2 a3) -> (([]) a1) -> (([]) 
           a2) -> (List_R a1 a2 a3) -> List_R a1 a2 a3
sortN_R leT_UU2081_ leT_UU2082_ leT_R _ _ s_R =
  case s_R of {
   List_R_nil_R -> List_R_nil_R;
   List_R_cons_R x_UU2081_ x_UU2082_ x_R s_UU2081_ s_UU2082_ s_R0 ->
    let {
     sortNrec_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 =
       case s_R1 of {
        List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
           Prelude.False Bool_R_false_R ((:) x_UU2081_0 ([])) ((:) x_UU2082_0
           ([])) (List_R_cons_R x_UU2081_0 x_UU2082_0 x_R0 ([]) ([])
           List_R_nil_R) stack_UU2081_ stack_UU2082_ stack_R;
        List_R_cons_R y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2 ->
         case leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R of {
          Bool_R_true_R ->
           incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 ((:) x_UU2081_0 ([])) ((:) x_UU2082_0
             ([])) (List_R_cons_R x_UU2081_0 x_UU2082_0 x_R0 ([]) ([])
             List_R_nil_R);
          Bool_R_false_R ->
           decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 ((:) x_UU2081_0 ([])) ((:) x_UU2082_0
             ([])) (List_R_cons_R x_UU2081_0 x_UU2082_0 x_R0 ([]) ([])
             List_R_nil_R)}};
     incr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
       case s_R1 of {
        List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
           Prelude.False Bool_R_false_R
           (catrev accu_UU2081_ ((:) x_UU2081_0 ([])))
           (catrev accu_UU2082_ ((:) x_UU2082_0 ([])))
           (let {
             catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
               case s1_R of {
                List_R_nil_R -> s2_R;
                List_R_cons_R x_UU2081_1 x_UU2082_1 x_R1 s1'_UU2081_
                 s1'_UU2082_ s1'_R ->
                 catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_1
                   s2_UU2081_) ((:) x_UU2082_1 s2_UU2082_) (List_R_cons_R
                   x_UU2081_1 x_UU2082_1 x_R1 s2_UU2081_ s2_UU2082_ s2_R)}}
            in catrev_R accu_UU2081_ accu_UU2082_ accu_R ((:) x_UU2081_0
                 ([])) ((:) x_UU2082_0 ([])) (List_R_cons_R x_UU2081_0
                 x_UU2082_0 x_R0 ([]) ([]) List_R_nil_R)) stack_UU2081_
           stack_UU2082_ stack_R;
        List_R_cons_R y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2 ->
         case leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R of {
          Bool_R_true_R ->
           incr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 ((:) x_UU2081_0 accu_UU2081_) ((:)
             x_UU2082_0 accu_UU2082_) (List_R_cons_R x_UU2081_0 x_UU2082_0
             x_R0 accu_UU2081_ accu_UU2082_ accu_R);
          Bool_R_false_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_
               (catrev accu_UU2081_ ((:) x_UU2081_0 ([]))) stack_UU2081_)
             (merge_sort_push leT_UU2082_
               (catrev accu_UU2082_ ((:) x_UU2082_0 ([]))) stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R
               (catrev accu_UU2081_ ((:) x_UU2081_0 ([])))
               (catrev accu_UU2082_ ((:) x_UU2082_0 ([])))
               (let {
                 catrev_R _ _ s1_R s2_UU2081_ s2_UU2082_ s2_R =
                   case s1_R of {
                    List_R_nil_R -> s2_R;
                    List_R_cons_R x_UU2081_1 x_UU2082_1 x_R1 s1'_UU2081_
                     s1'_UU2082_ s1'_R ->
                     catrev_R s1'_UU2081_ s1'_UU2082_ s1'_R ((:) x_UU2081_1
                       s2_UU2081_) ((:) x_UU2082_1 s2_UU2082_) (List_R_cons_R
                       x_UU2081_1 x_UU2082_1 x_R1 s2_UU2081_ s2_UU2082_ s2_R)}}
                in catrev_R accu_UU2081_ accu_UU2082_ accu_R ((:) x_UU2081_0
                     ([])) ((:) x_UU2082_0 ([])) (List_R_cons_R x_UU2081_0
                     x_UU2082_0 x_R0 ([]) ([]) List_R_nil_R)) stack_UU2081_
               stack_UU2082_ stack_R) y_UU2081_ y_UU2082_ y_R s_UU2081_0
             s_UU2082_0 s_R2}};
     decr_R stack_UU2081_ stack_UU2082_ stack_R x_UU2081_0 x_UU2082_0 x_R0 _ _ s_R1 accu_UU2081_ accu_UU2082_ accu_R =
       case s_R1 of {
        List_R_nil_R ->
         merge_sort_pop_R leT_UU2081_ leT_UU2082_ leT_R Prelude.False
           Prelude.False Bool_R_false_R ((:) x_UU2081_0 accu_UU2081_) ((:)
           x_UU2082_0 accu_UU2082_) (List_R_cons_R x_UU2081_0 x_UU2082_0 x_R0
           accu_UU2081_ accu_UU2082_ accu_R) stack_UU2081_ stack_UU2082_
           stack_R;
        List_R_cons_R y_UU2081_ y_UU2082_ y_R s_UU2081_0 s_UU2082_0 s_R2 ->
         case leT_R x_UU2081_0 x_UU2082_0 x_R0 y_UU2081_ y_UU2082_ y_R of {
          Bool_R_true_R ->
           sortNrec_R
             (merge_sort_push leT_UU2081_ ((:) x_UU2081_0 accu_UU2081_)
               stack_UU2081_)
             (merge_sort_push leT_UU2082_ ((:) x_UU2082_0 accu_UU2082_)
               stack_UU2082_)
             (merge_sort_push_R leT_UU2081_ leT_UU2082_ leT_R ((:) x_UU2081_0
               accu_UU2081_) ((:) x_UU2082_0 accu_UU2082_) (List_R_cons_R
               x_UU2081_0 x_UU2082_0 x_R0 accu_UU2081_ accu_UU2082_ accu_R)
               stack_UU2081_ stack_UU2082_ stack_R) y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2;
          Bool_R_false_R ->
           decr_R stack_UU2081_ stack_UU2082_ stack_R y_UU2081_ y_UU2082_ y_R
             s_UU2081_0 s_UU2082_0 s_R2 ((:) x_UU2081_0 accu_UU2081_) ((:)
             x_UU2082_0 accu_UU2082_) (List_R_cons_R x_UU2081_0 x_UU2082_0
             x_R0 accu_UU2081_ accu_UU2082_ accu_R)}}}
    in sortNrec_R ([]) ([]) List_R_nil_R x_UU2081_ x_UU2082_ x_R s_UU2081_
         s_UU2082_ s_R0}

sort1_stable :: Function
sort1_stable =
  Pack (\_ -> sort1) (\_ _ _ -> sort1_R) (\_ -> sort1P)

sort2_stable :: Function
sort2_stable =
  Pack (\_ -> sort2) (\_ _ _ -> sort2_R) (\_ -> sort2P)

sort3_stable :: Function
sort3_stable =
  Pack (\_ -> sort3) (\_ _ _ -> sort3_R) (\_ -> sort3P)

sortN_stable :: Function
sortN_stable =
  Pack (\_ -> sortN) (\_ _ _ -> sortN_R) (\_ -> sortNP)

