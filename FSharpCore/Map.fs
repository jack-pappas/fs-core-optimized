(*

Copyright 2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

namespace FSharpCore

open System.Collections.Generic
open System.Diagnostics
open OptimizedClosures


(*  NOTE :  The core functions implementing the AVL tree algorithm were extracted into OCaml
            from the "AVL Trees" theory in the Archive of Formal Proofs:
                http://afp.sourceforge.net/entries/AVL-Trees.shtml
            using Isabelle/HOL 2013. The extracted code was adapted to F# (e.g., by adjusting
            the formatting, fixing incomplete pattern-matches), then some of the supporting functions
            (e.g., iter, fold) were modified to use mutable data structures internally to eliminate
            traversal overhead and increase performance.
 *)

/// AVL tree which serves as the internal representation of the Map type.
[<NoEquality; NoComparison>]
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type internal MapTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Value, Height
    | Node of MapTree<'T> * MapTree<'T> * 'T * uint32


/// Functional operators on AVL trees.
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal MapTree =

    /// Returns the height of an AVL tree's root node.
    let inline height (tree : MapTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Determines if an AVL tree is empty.
    let isEmpty (tree : MapTree<'T>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// Creates an AVL tree whose root node holds the specified value
    /// and the specified left and right subtrees.
    let inline internal create value l (r : MapTree<'T>) =
        Node (l, r, value, (max (height l) (height r)) + 1u)

    /// Creates an AVL tree containing the specified value.
    let singleton value : MapTree<'T> =
        create value Empty Empty

    let rec private mkt_bal_l n l (r : MapTree<'T>) =
        if height l = height r + 2u then
            match l with
            | Empty ->
                failwith "mkt_bal_l"
            | Node (ll, lr, ln, _) ->
                if height ll < height lr then
                    match lr with
                    | Empty ->
                        failwith "mkt_bal_l"
                    | Node (lrl, lrr, lrn, _) ->
                        create lrn (create ln ll lrl) (create n lrr r)
                else
                    create ln ll (create n lr r)
        else
            create n l r

    let rec private mkt_bal_r n l (r : MapTree<'T>) =
        if height r = height l + 2u then
            match r with
            | Empty ->
                failwith "mkt_bal_r"
            | Node (rl, rr, rn, _) ->
                if height rr < height rl then
                    match rl with
                    | Empty ->
                        failwith "mkt_bal_r"
                    | Node (rll, rlr, rln, _) ->
                        create rln (create n l rll) (create rn rlr rr)
                else
                    create rn (create n l rl) rr
        else
            create n l r

    let rec private delete_max = function
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, (Node (_,_,_,_) as right), n, _) ->
            let na, r = delete_max right
            na, mkt_bal_l n l r

    let private delete_root = function
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (Empty, r, _, _) -> r
        | Node ((Node (_,_,_,_) as left), Empty, _, _) ->
            left
        | Node ((Node (_,_,_,_) as left), (Node (_,_,_,_) as right), _, _) ->
            let new_n, l = delete_max left
            mkt_bal_r new_n l right

    /// Implementation. Returns the height of an AVL tree.
    // OPTIMIZE : This should be re-implemented without continuations --
    // move it into 'computeHeight' and use a mutable stack to traverse the tree.
    let rec private computeHeightRec (tree : MapTree<'T>) cont =
        match tree with
        | Empty ->
            cont 0u
        | Node (l, r, _, _) ->
            computeHeightRec l <| fun height_l ->
            computeHeightRec r <| fun height_r ->
                (max height_l height_r) + 1u
                |> cont

    /// Returns the height of an AVL tree.
    let internal computeHeight (tree : MapTree<'T>) =
        computeHeightRec tree id
        
    /// Determines if an AVL tree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle theory.
    let rec internal avl = function
        | Empty -> true
        | Node (l, r, x, h) ->
            let height_l = computeHeight l
            let height_r = computeHeight r
            height_l = height_r
            || (height_l = (1u + height_r) || height_r = (1u + height_l))
            && h = ((max height_l height_r) + 1u)
            && avl l
            && avl r

    /// Determines if an AVL tree contains a specified value.
    let rec contains value (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            false
        | Node (l, r, n, _) ->
            let comparison = compare value n
            if comparison = 0 then      // value = n
                true
            elif comparison < 0 then    // value < n
                contains value l
            else                        // value > n
                contains value r

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec delete x (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            Empty
        | Node (l, r, n, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then      // x = n
                delete_root tree
            elif comparison < 0 then    // x < n
                let la = delete x l
                mkt_bal_r n la r
            else                        // x > n
                let a = delete x r
                mkt_bal_l n l a

    /// Adds a value to an AVL tree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    let rec insert x (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            Node (Empty, Empty, x, 1u)
        | Node (l, r, n, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then      // x = n
                tree
            elif comparison < 0 then    // x < n
                mkt_bal_l n (insert x l) r
            else                        // x > n
                mkt_bal_r n l (insert x r)

    /// Gets the maximum (greatest) value stored in the AVL tree.
    let rec maxElement (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (_, Empty, n, _) ->
            n
        | Node (_, (Node (_,_,_,_) as right), _, _) ->
            maxElement right

    /// Gets the minimum (least) value stored in the AVL tree.
    let rec minElement (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, _, n, _) ->
            n
        | Node ((Node (_,_,_,_) as left), _, _, _) ->
            minElement left

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private foldRec (folder : FSharpFunc<'State, _, 'State>) (state : 'State) (tree : MapTree<'T>) cont =
        match tree with
        | Empty ->
            cont state
        | Node (l, r, n, _) ->
            // Fold over the left subtree first.
            foldRec folder state l <| fun state ->
                // Apply the folder function to this node's value.
                let state = folder.Invoke (state, n)

                // Fold over the right subtree.
                foldRec folder state r cont

    /// Applies the given accumulating function to all elements in an AVL tree.
    let fold (folder : 'State -> _ -> 'State) (state : 'State) (tree : MapTree<'T>) =
        // Call the recursive, CPS-based implementation.
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldRec folder state tree id

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private foldBackRec (folder : FSharpFunc<_, 'State, 'State>) (tree : MapTree<'T>) (state : 'State) cont =
        match tree with
        | Empty ->
            cont state
        | Node (l, r, n, _) ->
            // Fold over the right subtree first.
            foldBackRec folder r state <| fun state ->
                // Apply the folder function to this node's value.
                let state = folder.Invoke (n, state)

                // Fold backwards over the left subtree.
                foldBackRec folder l state cont

    /// Applies the given accumulating function to all elements in an AVL tree.
    let foldBack (folder : _ -> 'State -> 'State) (tree : MapTree<'T>) (state : 'State) =
        // Call the recursive, CPS-based implementation.
        let folder = FSharpFunc<_,_,_>.Adapt folder
        foldBackRec folder tree state id

    /// Implementation.
    /// Applies the given accumulating function to all elements in an AVL tree.
    let rec private iterRec (action : _ -> unit) (tree : MapTree<'T>) cont =
        match tree with
        | Empty ->
            cont ()
        | Node (l, r, n, _) ->
            // Iterate over the left subtree first.
            iterRec action l <| fun () ->
                // Apply the action to this node's value.
                action n

                // Iterate over the right subtree.
                iterRec action r cont

    /// Applies the given function to each element stored in
    /// an AVL tree, in order from least to greatest.
    let iter (action : _ -> unit) (tree : MapTree<'T>) =
        iterRec action tree id

    /// Counts the number of elements in the tree.
    let count (tree : MapTree<'T>) =
        (0, tree)
        ||> fold (fun count _ ->
            count + 1)

    /// Extracts the minimum (least) value from an AVL tree,
    /// returning the value along with the updated tree.
    let rec extractMin (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, r, n, _) ->
            n, r
        | Node (Node (left, mid, a, _), r, x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the minimum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = create x mid r
            create a left n
            |> extractMin

    /// Extracts the minimum (least) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMin (tree : MapTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let minElement, tree = extractMin tree
            Some minElement, tree

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    let rec extractMax (tree : MapTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, Node (mid, right, a, _), x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the maximum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = create x l mid
            create a n right
            |> extractMax

    /// Extracts the maximum (greatest) value from an AVL tree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    let tryExtractMax (tree : MapTree<'T>) =
        // Is the tree empty?
        if isEmpty tree then
            None, tree
        else
            let maxElement, tree = extractMax tree
            Some maxElement, tree

    /// Merges two AVL trees and returns the result.
    let union (tree1 : MapTree<'T>) (tree2 : MapTree<'T>) =
        let tree1_count = count tree1
        let tree2_count = count tree2

        // Merge the smaller set into the larger set.
        if tree1_count < tree2_count then
            (tree2, tree1)
            ||> fold (fun tree el ->
                insert el tree)
        else
            (tree1, tree2)
            ||> fold (fun tree el ->
                insert el tree)

    /// Builds a new AVL tree from the elements of a sequence.
    let ofSeq (sequence : seq<_>) : MapTree<'T> =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            insert el tree)

    /// Builds a new AVL tree from the elements of an F# list.
    let ofList (list : _ list) : MapTree<'T> =
        (Empty, list)
        ||> List.fold (fun tree el ->
            insert el tree)

    /// Builds a new AVL tree from the elements of an array.
    let ofArray (array : _[]) : MapTree<'T> =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            insert el tree)

    /// Returns a sequence containing the elements stored
    /// in an AVL tree, ordered from least to greatest.
    let rec toSeq (tree : MapTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (l, r, n, _) ->
            yield! toSeq l
            yield n
            yield! toSeq r
        }

    /// Returns a sequence containing the elements stored in
    /// an AVL tree, ordered from greatest to least.
    let rec toSeqRev (tree : MapTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (l, r, n, _) ->
            yield! toSeq r
            yield n
            yield! toSeq l
        }
    
    /// Returns an F# list containing the elements stored in
    /// an AVL tree, ordered from least to greatest. 
    let toList (tree : MapTree<'T>) =
        (tree, [])
        ||> foldBack (fun el lst ->
            el :: lst)

    /// Returns an F# list containing the elements stored in
    /// an AVL tree, ordered from greatest to least.
    let toListRev (tree : MapTree<'T>) =
        ([], tree)
        ||> fold (fun lst el ->
            el :: lst)

    /// Returns an array containing the elements stored in
    /// an AVL tree, ordered from least to greatest.
    let toArray (tree : MapTree<'T>) =
        let elements = ResizeArray ()
        iter elements.Add tree
        elements.ToArray ()