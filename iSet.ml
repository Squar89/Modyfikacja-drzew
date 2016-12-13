(*
 * PSet - Polymorphic sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl
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

let (+.) x y = 
  if x = max_int
  || y = max_int
  || x > max_int - y
  || y > max_int - x
  then max_int
  else x + y

(* lewe poddrzewo * przedział * prawe poddrzewo * wysokość drzewa * below *)
type t =
  | Empty
  | Node of t * (int * int) * t * int * int

let empty = Empty

let is_empty s =
  s = Empty

let belong x (a, b) =
  (x >= a && x <= b)

let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0
  
let range (a, b) = 
  b - a + 1

let mem x s =
  let rec loop = function
    | Node (l, ((a, b) as p), r, _, _) ->
      if belong x p then true
      else if x < a then loop l
      else (* x > b *) loop r
    | Empty -> false
  in
  loop s

let bel = function
  | Node (_, p, _, _, x) -> x +. (range p)
  | Empty -> 0

let make l p r =
  Node (l, p, r, max (height l) (height r) + 1, (bel l +. bel r))

let below x s =
  let rec loop acc = function
    | Node (l, ((a, b) as p), r, _, _) ->
      if belong x (a, b) then
        acc +. (bel l +. range (a, x))
      else if x < a then
        loop acc l
      else (* x > b *)
        let acc = bel l +. range p in
        loop acc r
    | Empty -> acc
  in
  loop 0 s

let iter f s =
  let rec loop = function
    | Empty -> ()
    | Node (l, p, r,_ , _) -> loop l; f p; loop r
  in
  loop s

let fold f s acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, p, r, _, _) ->
      loop (f p (loop acc l)) r
  in
  loop acc s

let elements s = 
  let rec loop acc = function
    | Empty -> acc
    | Node(l, p, r, _, _) ->
          loop (p :: loop acc r) l in
  loop [] s

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
  
let add_simple (a, b) s =
  match s with
  | Node (_, (a1, b1), _, _, _) ->
    if a > b1 then
      bal (make s (a, b) empty)
    else if b < a1 then
      bal (make empty (a, b) s)
    else assert false
  | Empty -> make empty (a, b) empty
    
let rec join l p r =
  match (l, r) with
  | (Empty, _) -> add_simple p r
  | (_, Empty) -> add_simple p l
  | (Node(ll, lp, lr, lh, _), Node(rl, rp, rr, rh, _)) ->
      if lh > rh + 2 then bal (make ll lp (join lr p r))
      else if rh > lh + 2 then bal (make (join l p rl) rp rr)
      else make l p r

let rec min_elt = function
  | Node (Empty, p, _, _, _) -> p
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, p, r, _, _) -> bal ( make (remove_min_elt l) p r)
  | Empty -> invalid_arg "ISet.remove_min_elt"

let merge s1 s2 =
  match s1, s2 with
  | Empty, _ -> s2
  | _, Empty -> s1
  | _ ->
      let p = min_elt s2 in
      bal (make s1 p (remove_min_elt s2))
  
let split x s =
  let rec loop = function
    | Empty ->
      (Empty, false, Empty)
    | Node (l, ((a, b) as p), r, h, _) ->
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
  
let remove (x, y) s =
  let (l, _, _) = split x s in
  let (_, _, r) = split y s in
  merge l r

let add (x, y) s =
  let (l, _, _) = split x s in
  let (_, _, r) = split y s in
  join l (x, y) r