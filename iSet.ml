(*  Autor - Jakub Wróblewski 386401 gr. 5
    Recenzent - Karol Waszczuk 386488 gr. 2
*)
(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz, Jakub Wróblewski
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint.
*)


(* funkcja modyfikująca dodawanie, zapobiega wyjściu poza max_int *)
let (+.) x y =
  if x < 0 || y < 0 then x + y
  else  if x = max_int
    || y = max_int
    || x > max_int - y
    || y > max_int - x
    then max_int
  else x + y

(* typ drzewa, składający się z:
 * lewego poddrzewa * domkniętego przedziału * prawego poddrzewo *
 * wysokości drzewa * liczby wartości w przedziałach poddrzew danego drzewa *)
type t =
  | Empty
  | Node of t * (int * int) * t * int * int

let empty = Empty

let is_empty s =
  s = Empty

(* funkcja sprawdzająca czy x zawiera się w przedziale [a, b] *)
let belong x (a, b) =
  (x >= a && x <= b)

(* funkcja zwracająca wysokość danego drzewa *)
let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0

(* funkcja zwracająca liczbę wartości danego przedziału *)
let range (a, b) =
  if b - a + 1 <= 0 then max_int else b - a + 1

(* funkcja zwracająca liczbę wartości danego drzewa *)
let bel = function
  | Node (_, p, _, _, x) -> x +. (range p)
  | Empty -> 0

(* funkcja tworząca drzewo z dwóch poddrzew i przedziału *)
(* zawsze zachodzi warunek l < p < r *)
let make l p r =
  Node (l, p, r, max (height l) (height r) + 1, (bel l +. bel r))

(* funkcja zwracająca true jeśli x znajduje się w drzewie lub false w p.p. *)
let mem x s =
  let rec loop = function
    | Node (l, ((a, b) as p), r, _, _) ->
      if belong x p then true
      else if x < a then loop l
      else (* x > b *) loop r
    | Empty -> false
  in
  loop s

(* funkcja zwracająca liczbę wartości mniejszych lub równych od x
 * znajdujących się na drzewie *)
let below x s =
  let rec loop acc = function
    | Node (l, ((a, b) as p), r, _, _) ->
      if belong x (a, b) then
        acc +. (bel l +. range (a, x))
      else if x < a then
        loop acc l
      else (* x > b *)
        loop (acc +. (bel l +. range p)) r
    | Empty -> acc
  in
  loop 0 s

(* funkcja balansująca dane drzewo *)
let rec bal s =
  match s with
  | Node (l, p, r, _, _) ->
    let hl = height l in
    let hr = height r in
    if hl > hr + 2 then
    match l with
    | Node (ll, lp, lr, _, _) ->
      if height ll >= height lr then bal (make ll lp (make lr p r))
      else
        (match lr with
        | Node (lrl, lrp, lrr, _, _) ->
          bal (make (make ll lp lrl) lrp (make lrr p r))
        | Empty -> assert false)
    | Empty -> assert false
    else if hr > hl + 2 then
    match r with
    | Node (rl, rp, rr, _, _) ->
      if height rr >= height rl then bal (make (make l p rl) rp rr)
      else
        (match rl with
        | Node (rll, rlp, rlr, _, _) ->
          make (make l p rll) rlp (make rlr rp rr)
        | Empty -> assert false)
    | Empty -> assert false
    else make l p r
  | Empty -> s

(* funkcje zwracające odpowiednio najmniejszy i największy przedział w
 * danym drzewie *)
let rec min_elt = function
  | Node (Empty, p, _, _, _) -> p
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec max_elt = function
  | Node (_, p, Empty, _, _) -> p
  | Node (_, _, r, _, _) -> max_elt r
  | Empty -> raise Not_found

(* funkcje usuwające odpowiednio najmniejszy i największy przedział w
 * danym drzewie *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, p, r, _, _) -> bal (make (remove_min_elt l) p r)
  | Empty -> invalid_arg "ISet.remove_min_elt"

let rec remove_max_elt = function
  | Node (l, _, Empty, _, _) -> l
  | Node (l, p, r, _, _) -> bal (make l p (remove_max_elt r))
  | Empty -> invalid_arg "ISet.remove_max_elt"

(* funkcja zwracająca drzewo s powiększone o przedział (a, b) *)
(* przedział jest zawsze większy lub mniejszy od wszystkich elementów
 * danego drzewa *)
let add_simple (a, b) s =
  match s with
  | Node (_, (a1, b1), _, _, _) ->
    if a > b1 then
      bal (make s (a, b) empty)
    else if b < a1 then
      bal (make empty (a, b) s)
    else assert false
  | Empty -> make empty (a, b) empty

(* funkcja łącząca dwa drzewa i przedział *)
(* zawsze zachodzi warunek l < p < r *)
let rec join l p r =
  match (l, r) with
  | (Empty, _) -> add_simple p r
  | (_, Empty) -> add_simple p l
  | (Node(ll, lp, lr, lh, _), Node(rl, rp, rr, rh, _)) ->
      if lh > rh + 2 then bal (make ll lp (join lr p r))
      else if rh > lh + 2 then bal (make (join l p rl) rp rr)
      else make l p r

(* funkcja scalająca dwa drzewa w jedno *)
let merge s1 s2 =
  match s1, s2 with
  | Empty, _ -> s2
  | _, Empty -> s1
  | _ ->
      let p = min_elt s2 in
      bal (make s1 p (remove_min_elt s2))

(* funkcja zwracająca (poddrzewo złożone z elementów ostro mniejszych od x,
 * true jeśli x jest elementem pierwotnego drzewa false w p.p.,
 * poddrzewo złożone z elementów ostro większych od x *)
let split x s =
  let rec loop = function
    | Empty ->
      (Empty, false, Empty)
    | Node (l, ((a, b) as p), r, _, _) ->
      if belong x p then
        let lesser =
          if a = x then l else add_simple (a, x - 1) l in
        let greater =
          if b = x then r else add_simple (x + 1, b) r in
        (lesser, true, greater)
      else if x < a then
        let (ll, pres, rl) = loop l in (ll, pres, (join rl p r))
      else (* x > b *)
        let (lr, pres, rr) = loop r in ((join l p lr), pres, rr)
  in
  loop s

(* funkcja usuwająca przedział (x, y) z drzewa s *)
let remove (x, y) s =
  let (l, _, _) = split x s in
  let (_, _, r) = split y s in
  merge l r

(* funkcja dodająca przedział (x, y) do drzewa s *)
let add (x, y) s =
  let fix_intervals_left (l, (x, y), r) =
    if is_empty l then bal (make l (x, y) r)
    else
      let (a, b) = max_elt l in
      if b +. 1 = x then bal (make (remove_max_elt l) (a, y) r)
      else bal (make l (x, y) r)
  in
  let fix_intervals_right l (x, y) r =
    if is_empty r then (l, (x, y), r)
    else
      let (a, b) = min_elt r in
      if y +. 1 = a then (l, (x, b), (remove_min_elt r))
      else (l, (x, y), r)
  in
  match s with
  | Empty -> make empty (x, y) empty
  | _ ->
    let (l, _, _) = split x s in
    let (_, _, r) = split y s in
    fix_intervals_left (fix_intervals_right l (x, y) r)

(* aplikuje każdy przedział drzewa do f w rosnącym porządku *)
let iter f s =
  let rec loop = function
    | Empty -> ()
    | Node (l, p, r,_ , _) -> loop l; f p; loop r
  in
  loop s

(* "składa" funkcję w rosnącym porządku *)
let fold f s acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, p, r, _, _) ->
      loop (f p (loop acc l)) r
  in
  loop acc s

(* zwraca listę przedziałów drzewa w rosnącym porządku *)
let elements s =
  let rec loop acc = function
    | Empty -> acc
    | Node(l, p, r, _, _) ->
          loop (p :: loop acc r) l in
  loop [] s
