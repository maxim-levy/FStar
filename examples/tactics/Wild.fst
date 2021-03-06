module Wild

open FStar.Tactics
open FStar.Classical

let id x = x

(* Sanity checks that we're properly tracking implicits *)
[@(expect_failure [217])] let _ = assert False by (fun () -> exact (quote (id _)))
[@(expect_failure [217])] let _ = assert True  by (fun () -> exact (quote (id _)))
[@(expect_failure [217])] let _ = assert False by (fun () -> exact (quote _))
[@(expect_failure [217])] let _ = assert True  by (fun () -> exact (quote _))

(* A more elaborate test *)

val exists_weaken: #a:Type -> p:(a -> Type) -> q:(a -> Type) -> h:(forall (x:a{p x}). q x) -> x:a{p x}
  -> GTot (squash (exists x. q x))
let exists_weaken #a p q h x = exists_intro q x

val a : Type0
let a = unit

val p : a -> Type0
let p x = True

val q : a -> Type0
let q x = False

val fact: (h:squash (exists x. p x)) -> Lemma (exists x. q x)

[@(expect_failure [217])]
let fact h =
   assert (exists x. q x) by
     (fun _ ->
       apply_lemma (`exists_elim);
       exact (quote h);
       exact (quote (fun x -> exists_weaken p q _ x)))
