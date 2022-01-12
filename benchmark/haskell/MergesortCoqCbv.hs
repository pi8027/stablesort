module MergesortCoqCbv where

import qualified Prelude

type Pred t = t -> Prelude.Bool

type Rel t = t -> Pred t

catrev :: (([]) a1) -> (([]) a1) -> ([]) a1
catrev s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) x s1' -> catrev s1' ((:) x s2)}

rev :: (([]) a1) -> ([]) a1
rev s =
  catrev s ([])

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
        Prelude.True -> incr stack y s0 ((:) x ([]));
        Prelude.False -> decr stack y s0 ((:) x ([]))}};
   incr stack x s accu =
     case s of {
      ([]) ->
       merge_sort_pop leT Prelude.False (catrev accu ((:) x ([]))) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True -> incr stack y s0 ((:) x accu);
        Prelude.False ->
         sortNrec0 (merge_sort_push leT (catrev accu ((:) x ([]))) stack) y
           s0}};
   decr stack x s accu =
     case s of {
      ([]) -> merge_sort_pop leT Prelude.False ((:) x accu) stack;
      (:) y s0 ->
       case leT x y of {
        Prelude.True ->
         sortNrec0 (merge_sort_push leT ((:) x accu) stack) y s0;
        Prelude.False -> decr stack y s0 ((:) x accu)}}}
  in sortNrec0

sortN :: (Rel a1) -> (([]) a1) -> ([]) a1
sortN leT s =
  case s of {
   ([]) -> ([]);
   (:) x s0 -> sortNrec leT ([]) x s0}

