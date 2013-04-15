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
type internal MapTree<'Key, 'Value when 'Key : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Key, Value, Height
    | Node of MapTree<'Key, 'Value> * MapTree<'Key, 'Value> * KeyValuePair<'Key, 'Value> * uint32

#if CHECKED
    /// Implementation. Returns the height of a MapTree.
    static member private ComputeHeightRec (tree : MapTree<'Key, 'Value>) cont =
        match tree with
        | Empty ->
            cont 0u
        | Node (l, r, _, _) ->
            MapTree.ComputeHeightRec l <| fun height_l ->
            MapTree.ComputeHeightRec r <| fun height_r ->
                (max height_l height_r) + 1u
                |> cont

    /// Returns the height of a MapTree.
    static member private ComputeHeight (tree : MapTree<'Key, 'Value>) =
        MapTree.ComputeHeightRec tree id
        
    /// Determines if a MapTree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle/HOL theory.
    static member private AvlInvariant (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> true
        | Node (l, r, _, h) ->
            let height_l = MapTree.ComputeHeight l
            let height_r = MapTree.ComputeHeight r
            height_l = height_r
            || (height_l = (1u + height_r) || height_r = (1u + height_l))
            && h = ((max height_l height_r) + 1u)
            && MapTree.AvlInvariant l
            && MapTree.AvlInvariant r
#endif

    /// Returns the height of a MapTree.
    static member inline private Height (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Determines if a MapTree is empty.
    static member inline IsEmptyTree (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// Creates a MapTree whose root node holds the specified value
    /// and the specified left and right subtrees.
    static member inline private Create kvp l (r : MapTree<'Key, 'Value>) =
        Node (l, r, kvp, (max (MapTree.Height l) (MapTree.Height r)) + 1u)

    /// Creates a MapTree containing the specified key-value pair.
    static member Singleton kvp : MapTree<'Key, 'Value> =
        MapTree.Create kvp Empty Empty

    static member private mkt_bal_l n l (r : MapTree<'Key, 'Value>) =
        if MapTree.Height l = MapTree.Height r + 2u then
            match l with
            | Empty ->
                failwith "mkt_bal_l"
            | Node (ll, lr, ln, _) ->
                if MapTree.Height ll < MapTree.Height lr then
                    match lr with
                    | Empty ->
                        failwith "mkt_bal_l"
                    | Node (lrl, lrr, lrn, _) ->
                        MapTree.Create lrn (MapTree.Create ln ll lrl) (MapTree.Create n lrr r)
                else
                    MapTree.Create ln ll (MapTree.Create n lr r)
        else
            MapTree.Create n l r

    static member private mkt_bal_r n l (r : MapTree<'Key, 'Value>) =
        if MapTree.Height r = MapTree.Height l + 2u then
            match r with
            | Empty ->
                failwith "mkt_bal_r"
            | Node (rl, rr, rn, _) ->
                if MapTree.Height rr < MapTree.Height rl then
                    match rl with
                    | Empty ->
                        failwith "mkt_bal_r"
                    | Node (rll, rlr, rln, _) ->
                        MapTree.Create rln (MapTree.Create n l rll) (MapTree.Create rn rlr rr)
                else
                    MapTree.Create rn (MapTree.Create n l rl) rr
        else
            MapTree.Create n l r

    static member private DeleteMax (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, (Node (_,_,_,_) as right), n, _) ->
            let na, r = MapTree.DeleteMax right
            na, MapTree.mkt_bal_l n l r

    static member private DeleteRoot (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (Empty, r, _, _) -> r
        | Node ((Node (_,_,_,_) as left), Empty, _, _) ->
            left
        | Node ((Node (_,_,_,_) as left), (Node (_,_,_,_) as right), _, _) ->
            let new_n, l = MapTree.DeleteMax left
            MapTree.mkt_bal_r new_n l right

    /// Determines if a MapTree contains a specified value.
    static member ContainsKey key (tree : MapTree<'Key, 'Value>) : bool =
        match tree with
        | Empty ->
            false
        | Node (l, r, kvp, _) ->
            let comparison = compare key kvp.Key
            if comparison = 0 then      // key = k
                true
            elif comparison < 0 then    // key < k
                MapTree.ContainsKey key l
            else                        // key > k
                MapTree.ContainsKey key r

    /// Try to find a value associated with the specified key in a MapTree.
    static member TryFind key (tree : MapTree<'Key, 'Value>) : 'Value option =
        match tree with
        | Empty ->
            None
        | Node (l, r, kvp, _) ->
            let comparison = compare key kvp.Key
            if comparison = 0 then      // key = k
                Some kvp.Value
            elif comparison < 0 then    // key < k
                MapTree.TryFind key l
            else                        // key > k
                MapTree.TryFind key r

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Delete key (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty ->
            Empty
        | Node (l, r, kvp, _) as tree ->
            let comparison = compare key kvp.Key
            if comparison = 0 then              // key = k
                MapTree.DeleteRoot tree
            elif comparison < 0 then            // key < k
                let la = MapTree.Delete key l
                MapTree.mkt_bal_r kvp la r
            else                                // key > k
                let a = MapTree.Delete key r
                MapTree.mkt_bal_l kvp l a

    /// Adds a value to a MapTree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Insert (newKvp : KeyValuePair<_,_>) (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty ->
            Node (Empty, Empty, newKvp, 1u)
        | Node (l, r, kvp, h) as tree ->
            let comparison = compare newKvp.Key kvp.Key
            if comparison = 0 then                              // x = k
                // Try to determine if the new value is the same as the existing value;
                // if so, we can just return the original tree instead of creating a new one.
                if Unchecked.equals kvp.Value newKvp.Value then tree
                else
                    Node (l, r, newKvp, h)
            elif comparison < 0 then                            // x < k
                MapTree.mkt_bal_l kvp (MapTree.Insert newKvp l) r
            else                                                // x > k
                MapTree.mkt_bal_r kvp l (MapTree.Insert newKvp r)

    /// Counts the number of elements in the tree.
    static member Count (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> 0u
        | Node (Empty, Empty, _, _) -> 1u
        | Node (l, r, _, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The number of elements discovered in the tree so far.
            let mutable count = 1u   // Start at one (1) to include this root node.

            // Traverse the tree using the mutable stack, incrementing the counter at each node.
            stack.Push r
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                (* OPTIMIZATION: Handle a few of the cases specially here to avoid pushing empty
                   nodes on the stack. *)
                | Node (Empty, Empty, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                | Node (Empty, z, _, _)
                | Node (z, Empty, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, _, _) ->
                    // Increment the element count.
                    count <- count + 1u

                    // Push the children onto the stack.
                    stack.Push r
                    stack.Push l

            // Return the element count.
            count

    //
    static member Iter (action : 'Key -> 'Value -> unit) (tree : MapTree<'Key, 'Value>) : unit =
        match tree with
        | Empty -> ()
        | Node (Empty, Empty, kvp, _) ->
            // Invoke the action with this single element.
            action kvp.Key kvp.Value
        | Node (l, r, kvp, _) ->
            // Adapt the action function since we'll always supply all of the arguments at once.
            let action = FSharpFunc<_,_,_>.Adapt action

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply this value to the action function.
                    action.Invoke (kvp.Key, kvp.Value)

                | Node (Empty, z, kvp, _) ->
                    // Apply this value to the action function.
                    action.Invoke (kvp.Key, kvp.Value)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

    //
    static member IterKvp (action : KeyValuePair<'Key, 'Value> -> unit) (tree : MapTree<'Key, 'Value>) : unit =
        match tree with
        | Empty -> ()
        | Node (Empty, Empty, kvp, _) ->
            // Invoke the action with this single element.
            action kvp
        | Node (l, r, kvp, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply this value to the action function.
                    action kvp

                | Node (Empty, z, kvp, _) ->
                    // Apply this value to the action function.
                    action kvp

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

    /// Applies the given accumulating function to all elements in a MapTree.
    static member Fold (folder : 'State -> 'Key -> 'Value -> 'State) (state : 'State) (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, kvp, _) ->
            // Invoke the folder function on this single element and return the result.
            folder state kvp.Key kvp.Value
        | Node (l, r, kvp, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, kvp.Key, kvp.Value)

                | Node (Empty, z, kvp, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, kvp.Key, kvp.Value)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

            // Return the final state value.
            state

    /// Applies the given accumulating function to all elements in a MapTree.
    static member FoldBack (folder : 'Key -> 'Value -> 'State -> 'State) (state : 'State) (tree : MapTree<'Key, 'Value>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, kvp, _) ->
            // Invoke the folder function on this single element and return the result.
            folder kvp.Key kvp.Value state
        | Node (l, r, kvp, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push l
            stack.Push <| MapTree.Singleton kvp
            stack.Push r

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (kvp.Key, kvp.Value, state)

                | Node (z, Empty, kvp, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (kvp.Key, kvp.Value, state)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push l
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push r

            // Return the final state value.
            state

    //
    static member TryPick (picker : 'Key -> 'Value -> 'T option) (tree : MapTree<'Key, 'Value>) : 'T option =
        match tree with
        | Empty -> None
        | Node (Empty, Empty, kvp, _) ->
            // Apply the predicate function to this element and return the result.
            picker kvp.Key kvp.Value
        | Node (l, r, kvp, _) ->
            // Adapt the picker function since we'll always supply all of the arguments at once.
            let picker = FSharpFunc<_,_,_>.Adapt picker

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The picked value, if one has been picked.
            let mutable pickedValue = None

            // Traverse the tree using the mutable stack, applying the picker function to
            // each value to update 'pickedValue'.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 && Option.isNone pickedValue do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply the picker to this element.
                    pickedValue <- picker.Invoke (kvp.Key, kvp.Value)

                | Node (Empty, z, kvp, _) ->
                    // Apply the picker to this element.
                    pickedValue <- picker.Invoke (kvp.Key, kvp.Value)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

            // Return the picked value, if any.
            pickedValue

    /// Tests if any element of the collection satisfies the given predicate.
    static member Exists (predicate : 'Key -> 'Value -> bool) (tree : MapTree<'Key, 'Value>) : bool =
        match tree with
        | Empty -> false
        | Node (Empty, Empty, kvp, _) ->
            // Apply the predicate function to this element and return the result.
            predicate kvp.Key kvp.Value
        | Node (l, r, kvp, _) ->
            // Adapt the predicate since we'll always supply all of the arguments at once.
            let predicate = FSharpFunc<_,_,_>.Adapt predicate

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have we found a matching element?
            let mutable foundMatch = false

            // Traverse the tree using the mutable stack, applying the predicate function to
            // each value to update 'foundMatch'.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 && not foundMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate.Invoke (kvp.Key, kvp.Value)

                | Node (Empty, z, kvp, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate.Invoke (kvp.Key, kvp.Value)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

            // Return the value indicating whether or not a matching element was found.
            foundMatch

    /// Tests if all elements of the collection satisfy the given predicate.
    static member Forall (predicate : 'Key -> 'Value -> bool) (tree : MapTree<'Key, 'Value>) : bool =
        match tree with
        | Empty -> true
        | Node (Empty, Empty, kvp, _) ->
            // Apply the predicate function to this element and return the result.
            predicate kvp.Key kvp.Value
        | Node (l, r, kvp, _) ->
            // Adapt the predicate since we'll always supply all of the arguments at once.
            let predicate = FSharpFunc<_,_,_>.Adapt predicate

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have all of the elements we've seen so far matched the predicate?
            let mutable allElementsMatch = true

            // Traverse the tree using the mutable stack, applying the predicate function to
            // each value to update 'allElementsMatch'.
            stack.Push r
            stack.Push <| MapTree.Singleton kvp
            stack.Push l

            while stack.Count > 0 && allElementsMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, kvp, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate.Invoke (kvp.Key, kvp.Value)

                | Node (Empty, z, kvp, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate.Invoke (kvp.Key, kvp.Value)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, kvp, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| MapTree.Singleton kvp
                    stack.Push l

            // Return the value indicating if all elements matched the predicate.
            allElementsMatch

    /// Builds a new MapTree from the elements of a sequence.
    static member OfSeq (sequence : seq<'Key * 'Value>) : MapTree<'Key, 'Value> =
        (Empty, sequence)
        ||> Seq.fold (fun tree (key, value) ->
            MapTree.Insert (KeyValuePair (key, value)) tree)

    /// Builds a new MapTree from the elements of an list.
    static member OfList (list : ('Key * 'Value) list) : MapTree<'Key, 'Value> =
        (Empty, list)
        ||> List.fold (fun tree (key, value) ->
            MapTree.Insert (KeyValuePair (key, value)) tree)

    /// Builds a new MapTree from the elements of an array.
    static member OfArray (array : ('Key * 'Value)[]) : MapTree<'Key, 'Value> =
        (Empty, array)
        ||> Array.fold (fun tree (key, value) ->
            MapTree.Insert (KeyValuePair (key, value)) tree)

    /// Builds a new MapTree from an array of KeyValuePairs.
    static member OfKvpArray (array : KeyValuePair<_,_>[]) : MapTree<'Key, 'Value> =
        Array.foldBack MapTree.Insert array Empty

    (* NOTE : This works, but has been disabled for now because the existing F# Map
                implementation uses a custom IEnumerator implementation which has different
                characteristics; the unit tests expect to see these, so that implementation
                is used instead of this one (at least for now). *)
//    /// Returns a sequence containing the elements stored
//    /// in a MapTree, ordered from least to greatest.
//    static member ToSeq (tree : MapTree<'Key, 'Value>) =
//        seq {
//        match tree with
//        | Empty -> ()
//        | Node (l, r, n, _) ->
//            yield! MapTree.ToSeq l
//            yield n
//            yield! MapTree.ToSeq r
//        }

    /// Returns a list containing the elements stored in
    /// a MapTree, ordered from least to greatest. 
    static member ToList (tree : MapTree<'Key, 'Value>) =
        ([], tree)
        ||> MapTree.FoldBack (fun key value lst ->
            (key, value) :: lst)

    /// Returns an array containing the elements stored in
    /// a MapTree, ordered from least to greatest.
    static member ToArray (tree : MapTree<'Key, 'Value>) =
        let elements = ResizeArray ()
        tree |> MapTree.Iter (fun key value ->
            elements.Add (key, value))
        elements.ToArray ()

    /// Returns an array containing the elements stored in
    /// a MapTree, ordered from least to greatest.
    static member ToKvpArray (tree : MapTree<'Key, 'Value>) =
        let elements = ResizeArray ()
        MapTree.IterKvp elements.Add tree
        elements.ToArray ()

    static member private CompareStacks (l1 : MapTree<'Key, 'Value> list, l2 : MapTree<'Key, 'Value> list) : int =
        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | (Empty :: t1), (Empty :: t2) ->
            MapTree.CompareStacks (t1, t2)
        | (Node (Empty, Empty, n1kvp, _) :: t1), (Node (Empty, Empty, n2kvp, _) :: t2) ->
            match compare n1kvp.Key n2kvp.Key with
            | 0 ->
                MapTree.CompareStacks (t1, t2)
            | c -> c

        | (Node (Empty, Empty, n1kvp, _) :: t1), (Node (Empty, n2r, n2kvp, _) :: t2) ->
            match compare n1kvp.Key n2kvp.Key with
            | 0 ->
                MapTree.CompareStacks (Empty :: t1, n2r :: t2)
            | c -> c

        | (Node (Empty, n1r, n1kvp, _) :: t1), (Node (Empty, Empty, n2kvp, _) :: t2) ->
            match compare n1kvp.Key n2kvp.Key with
            | 0 ->
                MapTree.CompareStacks (n1r :: t1, Empty :: t2)
            | c -> c

        | (Node (Empty, n1r, n1kvp, _) :: t1), (Node (Empty, n2r, n2kvp, _) :: t2) ->
            match compare n1kvp.Key n2kvp.Key with
            | 0 ->
                MapTree.CompareStacks (n1r :: t1, n2r :: t2)
            | c -> c

        | ((Node (Empty, Empty, n1kvp, _) :: t1) as l1), _ ->
            MapTree.CompareStacks (Empty :: l1, l2)
        
        | (Node (n1l, n1r, n1kvp, _) :: t1), _ ->
            MapTree.CompareStacks (n1l :: Node (Empty, n1r, n1kvp, 0u) :: t1, l2)
        
        | _, ((Node (Empty, Empty, n2kvp, _) :: t2) as l2) ->
            MapTree.CompareStacks (l1, Empty :: l2)
        
        | _, (Node (n2l, n2r, n2kvp, _) :: t2) ->
            MapTree.CompareStacks (l1, n2l :: Node (Empty, n2r, n2kvp, 0u) :: t2)
                
    static member Compare (s1 : MapTree<'Key, 'Value>, s2 : MapTree<'Key, 'Value>) : int =
        match s1, s2 with
        | Empty, Empty -> 0
        | Empty, _ -> -1
        | _, Empty -> 1
        | _ ->
            MapTree<'Key, 'Value>.CompareStacks ([s1], [s2])

(*** Imperative left-to-right iterators. ***)

[<NoEquality; NoComparison>]
type internal MapIterator<'Key, 'Value when 'Key : comparison> = {
    // invariant: always collapseLHS result
    mutable stack: MapTree<'Key, 'Value> list;
    // true when MoveNext has been called
    mutable started : bool;
} with
    // collapseLHS:
    // a) Always returns either [] or a list starting with a 'leaf' node.
    // b) The "fringe" of the set stack is unchanged.
    static member private CollapseLHS stack =
        match stack with
        | [] -> []
        | Empty :: rest ->
            MapIterator<'Key, 'Value>.CollapseLHS rest
        | Node (Empty, Empty, _, _) :: _ ->
            stack
        | Node (l, r, n, _) :: rest ->
            MapIterator<'Key, 'Value>.CollapseLHS (l :: (Node (Empty, Empty, n, 0u)) :: r :: rest)

    //
    static member private MkIterator (s : MapTree<'Key, 'Value>) = {
        stack = MapIterator<'Key, 'Value>.CollapseLHS [s];
        started = false; }

    //
    static member private Current i =
        if i.started then
            match i.stack with
            | [] ->
                //raise (new System.InvalidOperationException(SR.GetString(SR.enumerationAlreadyFinished)))
                invalidOp "enumerationAlreadyFinished"
            | Node (Empty, Empty, kvp, _) :: _ -> kvp
            | _ -> failwith "Please report error: Map iterator, unexpected stack for current"
        else
            //raise (new System.InvalidOperationException(SR.GetString(SR.enumerationNotStarted)))
            invalidOp "enumerationNotStarted"

    //
    static member private MoveNext i =
        if i.started then
            match i.stack with
            | Node (Empty, Empty, _, _) :: rest ->
                i.stack <- MapIterator<'Key, 'Value>.CollapseLHS rest
                not i.stack.IsEmpty
            | [] -> false
            | _ -> failwith "Please report error: Map iterator, unexpected stack for moveNext"
        else
            i.started <- true       // The first call to MoveNext "starts" the enumeration.
            not i.stack.IsEmpty

    //
    static member mkIEnumerator (m : MapTree<'Key, 'Value>) =
        let i = ref (MapIterator.MkIterator m)
        { new System.Collections.Generic.IEnumerator<_> with
                member __.Current =
                    MapIterator<'Key, 'Value>.Current !i
            interface System.Collections.IEnumerator with
                member __.Current =
                    box <| MapIterator<'Key, 'Value>.Current !i
                member __.MoveNext () =
                    MapIterator<'Key, 'Value>.MoveNext !i
                member __.Reset () =
                    i := MapIterator<'Key, 'Value>.MkIterator m
            interface System.IDisposable with
                member __.Dispose () = () }


//
[<Sealed; CompiledName("FSharpMap`2")>]
#if FX_NO_DEBUG_PROXIES
#else
[<DebuggerTypeProxy(typedefof<MapDebugView<_,_>>)>]
#endif
#if FX_NO_DEBUG_DISPLAYS
#else
[<DebuggerDisplay("Count = {Count}")>]
#endif
[<CodeAnalysis.SuppressMessage("Microsoft.Naming", "CA1710:IdentifiersShouldHaveCorrectSuffix")>]
type Map<[<EqualityConditionalOn>] 'Key, [<EqualityConditionalOn;ComparisonConditionalOn>] 'Value when 'Key : comparison>
    private (tree : MapTree<'Key, 'Value>) =
    // We use .NET generics per-instantiation static fields to avoid allocating a new object for each empty
    // map (it is just a lookup into a .NET table of type-instantiation-indexed static fields).
    /// The empty map instance.
    static let empty : Map<'Key, 'Value> = Map Empty

#if FX_NO_BINARY_SERIALIZATION
#else
    // NOTE: This type is logically immutable. This field is only mutated during deserialization. 
    //[<System.NonSerialized>]
    //let mutable comparer : IComparer<'T> = null     // TODO : Can this be removed now? It's no longer used anywhere.

    // NOTE: This type is logically immutable. This field is only mutated during deserialization. 
    [<System.NonSerialized>]
    let mutable tree = tree
        
    // NOTE: This type is logically immutable. This field is only mutated during serialization and deserialization. 
    //
    // WARNING: The compiled name of this field may never be changed because it is part of the logical 
    // WARNING: permanent serialization format for this type.
    let mutable serializedData = null

    [<System.Runtime.Serialization.OnSerializingAttribute>]
    member __.OnSerializing (_ : System.Runtime.Serialization.StreamingContext) =
        //ignore(context)
        serializedData <- MapTree.ToKvpArray tree

    // Do not set this to null, since concurrent threads may also be serializing the data
    //[<System.Runtime.Serialization.OnSerializedAttribute>]
    //member __.OnSerialized(context: System.Runtime.Serialization.StreamingContext) =
    //    serializedData <- null

    [<System.Runtime.Serialization.OnDeserializedAttribute>]
    member __.OnDeserialized (_ : System.Runtime.Serialization.StreamingContext) =
        //ignore(context)
        //comparer <- LanguagePrimitives.FastGenericComparer<'Key>
        tree <- MapTree.OfKvpArray serializedData
        serializedData <- null
#endif

    /// The empty map instance.
#if FX_NO_DEBUG_DISPLAYS
#else
    [<DebuggerBrowsable(DebuggerBrowsableState.Never)>]
#endif
    static member internal Empty =
        empty

    //
    new (elements : seq<'Key * 'Value>) =
        // Preconditions
        // TODO : Check for null input.

        // OPTIMIZE : Try to cast the sequence to array or list;
        // if it succeeds use the specialized method for that type for better performance.
        Map (MapTree.OfSeq elements)

    //
    member private __.Tree
        with get () = tree

    //
    member __.Count
        with get () =
            int <| MapTree.Count tree

    //
    member __.IsEmpty
        with get () =
            match tree with
            | Empty -> true
            | Node (_,_,_,_) -> false

    //
    member __.Item
        with get (key : 'Key) =
            match MapTree.TryFind key tree with
            | None ->
                raise <| System.Collections.Generic.KeyNotFoundException ()
            | Some value ->
                value

    //
    member __.ContainsKey (key : 'Key) : bool =
        MapTree.ContainsKey key tree

    //
    member __.TryFind (key : 'Key) : 'Value option =
        MapTree.TryFind key tree

    //
    member this.Add (key : 'Key, value : 'Value) : Map<'Key, 'Value> =
        // Add the element to the MapTree; if the result is the same (i.e., the tree
        // already contained the element), return this set instead of creating a new one.
        let tree' = MapTree.Insert (KeyValuePair (key, value)) tree
        if System.Object.ReferenceEquals (tree, tree') then this
        else Map (tree')

    //
    member this.Remove (key : 'Key) : Map<'Key, 'Value> =
        // Remove the element from the MapTree; if the result is the same (i.e., the tree
        // did not contain the element), return this set instead of creating a new one.
        let tree' = MapTree.Delete key tree
        if System.Object.ReferenceEquals (tree, tree') then this
        else Map (tree')

    //
    static member internal Singleton key value : Map<'Key, 'Value> =
        Map (MapTree.Singleton (KeyValuePair (key, value)))

    //
    static member internal FromSeq (sequence : seq<'Key * 'Value>) : Map<'Key, 'Value> =
        // Preconditions
        // TODO : Check for null input

        Map (MapTree.OfSeq sequence)

    //
    static member internal FromList (list : ('Key * 'Value) list) : Map<'Key, 'Value> =
        // Preconditions
        // TODO : Check for null input

        Map (MapTree.OfList list)

    //
    static member internal FromArray (arr : ('Key * 'Value)[]) : Map<'Key, 'Value> =
        // Preconditions
        // TODO : Check for null input

        Map (MapTree.OfArray arr)

//    //
//    member internal this.ToSeq () : seq<'T> =
//        //MapTree.ToSeq tree
//        this :> seq<_>

    //
    member internal __.ToList () =
        MapTree.ToList tree

    //
    member internal __.ToArray () =
        MapTree.ToArray tree

    //
    member internal __.ToKvpArray () =
        MapTree.ToKvpArray tree

    //
    member internal __.Iterate (action : 'Key -> 'Value -> unit) : unit =
        MapTree.Iter action tree

    //
    member internal __.TryPick (picker : 'Key -> 'Value -> 'U option) : 'U option =
        MapTree.TryPick picker tree

    //
    member internal __.Exists (predicate : 'Key -> 'Value -> bool) : bool =
        MapTree.Exists predicate tree

    //
    member internal __.ForAll (predicate : 'Key -> 'Value -> bool) : bool =
        MapTree.Forall predicate tree

    //
    member internal __.Fold (folder : 'State -> 'Key -> 'Value -> 'State) (state : 'State) : 'State =
        MapTree.Fold folder state tree

    //
    member internal __.FoldBack (folder : 'Key -> 'Value -> 'State -> 'State) (state : 'State) : 'State =
        MapTree.FoldBack folder state tree

    //
    member internal __.Map (mapping : 'Key -> 'Value -> 'U) : Map<'Key, 'U> =
        let mappedTree =
            (MapTree.Empty, tree)
            ||> MapTree.Fold (fun mappedTree key value ->
                let mappedValue = mapping key value
                MapTree.Insert (KeyValuePair (key, mappedValue)) mappedTree)

        Map (mappedTree)

    //
    member internal __.Filter (predicate : 'Key -> 'Value -> bool) : Map<'Key, 'Value> =
        let filteredTree =
            (tree, tree)
            ||> MapTree.Fold (fun filteredTree key value ->
                if predicate key value then filteredTree
                else MapTree.Delete key filteredTree)

        Map (filteredTree)

    //
    member internal this.Partition (predicate : 'Key -> 'Value -> bool) : Map<'Key, 'Value> * Map<'Key, 'Value> =
        let trueTree, falseTree =
            ((tree, tree), tree)
            ||> MapTree.Fold (fun (trueTree, falseTree) key value ->
                if predicate key value then
                    trueTree,
                    MapTree.Delete key falseTree
                else
                    MapTree.Delete key trueTree,
                    falseTree)

        // If either of the 'true' or 'false' trees are equivalent to the input tree,
        // return this set as one component of the returned tuple -- this avoids creating
        // an additional set for no reason.
        if System.Object.ReferenceEquals (tree, trueTree) then
            this, empty
        elif System.Object.ReferenceEquals (tree, falseTree) then
            empty, this
        else
            Map (trueTree), Map (falseTree)

    // OPTIMIZE : Instead of computing this repeatedly -- this type is immutable so we should
    // lazily compute the hashcode once instead; however, we do need to account for the case
    // where an instance is created via deserialization, so it may make sense to use a 'ref'
    // field (which is excluded from serialization) with Interlocked.Exchange instead of using
    // a 'lazy' value.
    member __.ComputeHashCode () =
        let inline combineHash x y = (x <<< 1) + y + 631
        (0, tree)
        ||> MapTree.Fold (fun res x y ->
            let res = combineHash res (hash x)
            combineHash res (Unchecked.hash y))
        |> abs

    override this.GetHashCode () =
        this.ComputeHashCode ()

    // OPTIMIZE : Would it be significantly faster if we re-implemented this to work
    // directly on the MapTrees instead of using enumerators? Or, at least using an
    // imperative loop instead of a recursive function?
    override this.Equals other =
        match other with
        | :? Map<'Key, 'Value> as other ->
            use e1 = (this :> seq<_>).GetEnumerator ()
            use e2 = (other :> seq<_>).GetEnumerator ()
            let rec loop () =
                let m1 = e1.MoveNext ()
                let m2 = e2.MoveNext ()
                (m1 = m2)
                && (not m1 ||
                    ((e1.Current.Key = e2.Current.Key)
                    && (Unchecked.equals e1.Current.Value e2.Current.Value)
                    && loop ()))
            loop ()
        | _ -> false

    override x.ToString () =
        match List.ofSeq (Seq.truncate 4 x) with
        | [] -> "map []"
        | [KeyValue h1] ->
            System.Text.StringBuilder()
                .Append("map [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("]")
                .ToString()
        | [KeyValue h1;KeyValue h2] ->
            System.Text.StringBuilder()
                .Append("map [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("]")
                .ToString()
        | [KeyValue h1;KeyValue h2;KeyValue h3] ->
            System.Text.StringBuilder()
                .Append("map [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h3)
                .Append("]")
                .ToString()
        | KeyValue h1 :: KeyValue h2 :: KeyValue h3 :: _ ->
            System.Text.StringBuilder()
                .Append("map [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h3)
                .Append("; ... ]")
                .ToString()

    interface IEnumerable<KeyValuePair<'Key, 'Value>> with
        member m.GetEnumerator() = MapIterator.mkIEnumerator tree

    interface System.Collections.IEnumerable with
        member m.GetEnumerator() = (MapIterator.mkIEnumerator tree :> System.Collections.IEnumerator)

    interface IDictionary<'Key, 'Value> with
        member this.Item
            with get x = this.[x]
            and set _ _ =
                //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
                raise <| System.NotSupportedException "mapCannotBeMutated"

        // REVIEW: this implementation could avoid copying the Values to an array
        member this.Keys = ([| for kvp in this -> kvp.Key |] :> ICollection<'Key>)

        // REVIEW: this implementation could avoid copying the Values to an array
        member this.Values = ([| for kvp in this -> kvp.Value |] :> ICollection<'Value>)

        member __.Add (_, _) =
            //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
            raise <| System.NotSupportedException "mapCannotBeMutated"
        member this.ContainsKey k =
            this.ContainsKey k
        member this.TryGetValue (k, r) =
            if this.ContainsKey k then
                r <- this.[k]
                true
            else false
        member __.Remove (_ : 'Key) : bool =
            //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
            raise <| System.NotSupportedException "mapCannotBeMutated"

    interface ICollection<KeyValuePair<'Key, 'Value>> with
        member __.Add _ =
            //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
            raise <| System.NotSupportedException "mapCannotBeMutated"
        member __.Clear () =
            //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
            raise <| System.NotSupportedException "mapCannotBeMutated"
        member __.Remove _ =
            //raise <| System.NotSupportedException (SR.GetString SR.mapCannotBeMutated)
            raise <| System.NotSupportedException "mapCannotBeMutated"
        member this.Contains x =
            this.ContainsKey(x.Key) && Unchecked.equals this.[x.Key] x.Value
        member this.CopyTo (array, arrayIndex) : unit =
            // Preconditions
            if System.Object.ReferenceEquals (null, array) then
                nullArg "array"
            elif arrayIndex < 0 then
                raise <| System.ArgumentOutOfRangeException "arrayIndex"
            elif arrayIndex + (int (MapTree.Count tree)) > Array.length array then
                invalidArg "arrayIndex"
                    "There is not enough room in the array to copy the elements when starting at the specified index."

            arrayIndex
            |> this.Fold (fun index key value ->
                array.[index] <- KeyValuePair (key, value)
                index + 1)
            |> ignore

        member s.IsReadOnly =
            true
        member s.Count =
            s.Count

    interface System.IComparable with
        member m.CompareTo (obj: obj) =
            match obj with
            | :? Map<'Key, 'Value> as m2 ->
                (m, m2)
                ||> Seq.compareWith
                    (fun (kvp1 : KeyValuePair<_,_>) (kvp2 : KeyValuePair<_,_>) ->
                        match compare kvp1.Key kvp2.Key with
                        | 0 ->
                            Unchecked.compare kvp1.Value kvp2.Value
                        | c -> c)
            | _ ->
                //invalidArg "obj" (SR.GetString SR.notComparable)
                invalidArg "obj" "notComparable"

and [<Sealed>]
    internal MapDebugView<'Key, 'Value when 'Key : comparison> (map : Map<'Key, 'Value>) =

#if FX_NO_DEBUG_DISPLAYS
#else
    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
#endif
    member __.Items
        with get () : KeyValuePair<'Key, 'Value>[] =
            //map |> Seq.truncate mapDebugViewMaxElementCount |> Seq.toArray
            map.ToKvpArray ()

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Map =
    [<CompiledName("IsEmpty")>]
    let (*inline*) isEmpty (map:Map<_,_>) =
        map.IsEmpty

    [<CompiledName("Add")>]
    let (*inline*) add key value (map : Map<_,_>) =
        map.Add (key, value)

    [<CompiledName("Find")>]
    let (*inline*) find k (m:Map<_,_>) = m.[k]

    [<CompiledName("TryFind")>]
    let (*inline*) tryFind k (m:Map<_,_>) = m.TryFind(k)

    [<CompiledName("Remove")>]
    let (*inline*) remove k (m:Map<_,_>) = m.Remove(k)

    [<CompiledName("ContainsKey")>]
    let (*inline*) containsKey k (m:Map<_,_>) = m.ContainsKey(k)

    [<CompiledName("Iterate")>]
    let (*inline*) iter f (m:Map<_,_>) = m.Iterate(f)

    [<CompiledName("TryPick")>]
    let (*inline*) tryPick f (m:Map<_,_>) = m.TryPick(f)

    [<CompiledName("Pick")>]
    let pick f (m:Map<_,_>) =
        match tryPick f m with
        | None -> raise <| System.Collections.Generic.KeyNotFoundException ()
        | Some res -> res

    [<CompiledName("Exists")>]
    let (*inline*) exists f (m:Map<_,_>) = m.Exists(f)

    [<CompiledName("Filter")>]
    let (*inline*) filter f (m:Map<_,_>) = m.Filter(f)

    [<CompiledName("Partition")>]
    let (*inline*) partition f (m:Map<_,_>) = m.Partition(f)

    [<CompiledName("ForAll")>]
    let (*inline*) forall f (m:Map<_,_>) = m.ForAll(f)

//    let mapRange f (m:Map<_,_>) =
//        m.MapRange(f)

    [<CompiledName("Map")>]
    let (*inline*) map f (m:Map<_,_>) =
        m.Map(f)

    [<CompiledName("Fold")>]
    let (*inline*) fold<'Key,'T,'State when 'Key : comparison> f (z:'State) (m:Map<'Key,'T>) =
        m.Fold f z

    [<CompiledName("FoldBack")>]
    let (*inline*) foldBack<'Key,'T,'State  when 'Key : comparison> f (m:Map<'Key,'T>) (z:'State) =
        m.FoldBack f z
        
    [<CompiledName("ToSeq")>]
    let toSeq (m:Map<_,_>) =
        m |> Seq.map (fun kvp -> kvp.Key, kvp.Value)

    [<CompiledName("FindKey")>]
    let findKey f (m : Map<_,_>) =
        m |> toSeq |> Seq.pick (fun (k,v) -> if f k v then Some(k) else None)

    [<CompiledName("TryFindKey")>]
    let tryFindKey f (m : Map<_,_>) =
        m |> toSeq |> Seq.tryPick (fun (k,v) -> if f k v then Some(k) else None)

    [<CompiledName("OfList")>]
    let ofList (l: ('Key * 'Value) list) =
        Map<_,_>.FromList(l)

    [<CompiledName("OfSeq")>]
    let (*inline*) ofSeq sequence =
        Map<_,_> (sequence)

    [<CompiledName("OfArray")>]
    let ofArray (array: ('Key * 'Value)[]) =
        Map<_,_>.FromArray array

    [<CompiledName("ToList")>]
    let toList (m:Map<_,_>) =
        m.ToList()

    [<CompiledName("ToArray")>]
    let toArray (m:Map<_,_>) =
        m.ToArray()

    [<CompiledName("Empty")>]
    let empty<'Key,'Value  when 'Key : comparison> =
        Map<'Key,'Value>.Empty

