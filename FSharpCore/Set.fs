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


(*  NOTE :  The core functions implementing the SetTree algorithm were extracted into OCaml
            from the "AVL Trees" theory in the Archive of Formal Proofs:
                http://afp.sourceforge.net/entries/AVL-Trees.shtml
            using Isabelle/HOL 2013. The extracted code was adapted to F# (e.g., by adjusting
            the formatting, fixing incomplete pattern-matches), then some of the supporting functions
            (e.g., iter, fold) were modified to use mutable data structures internally to eliminate
            traversal overhead and increase performance.
*)

/// SetTree which serves as the internal representation of the Set type.
[<NoEquality; NoComparison>]
[<CompilationRepresentation(CompilationRepresentationFlags.UseNullAsTrueValue)>]
type internal SetTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Value, Height
    | Node of SetTree<'T> * SetTree<'T> * 'T * uint32

#if CHECKED
    /// Implementation. Returns the height of a SetTree.
    static member private ComputeHeightRec (tree : SetTree<'T>) cont =
        match tree with
        | Empty ->
            cont 0u
        | Node (l, r, _, _) ->
            SetTree.ComputeHeightRec l <| fun height_l ->
            SetTree.ComputeHeightRec r <| fun height_r ->
                (max height_l height_r) + 1u
                |> cont

    /// Returns the height of a SetTree.
    static member private ComputeHeight (tree : SetTree<'T>) =
        SetTree.ComputeHeightRec tree id
        
    /// Determines if a SetTree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle theory.
    static member private AvlInvariant (tree : SetTree<'T>) =
        match tree with
        | Empty -> true
        | Node (l, r, x, h) ->
            let height_l = SetTree.ComputeHeight l
            let height_r = SetTree.ComputeHeight r
            height_l = height_r
            || (height_l = (1u + height_r) || height_r = (1u + height_l))
            && h = ((max height_l height_r) + 1u)
            && SetTree.AvlInvariant l
            && SetTree.AvlInvariant r
#endif

    /// Returns the height of a SetTree.
    static member inline private Height (tree : SetTree<'T>) =
        match tree with
        | Empty -> 0u
        | Node (_,_,_,h) -> h

    /// Determines if a SetTree is empty.
    static member inline IsEmptyTree (tree : SetTree<'T>) =
        match tree with
        | Empty -> true
        | Node (_,_,_,_) -> false

    /// Creates a SetTree whose root node holds the specified value
    /// and the specified left and right subtrees.
    static member inline private Create value l (r : SetTree<'T>) =
        Node (l, r, value, (max (SetTree.Height l) (SetTree.Height r)) + 1u)

    /// Creates a SetTree containing the specified value.
    static member Singleton value : SetTree<'T> =
        SetTree.Create value Empty Empty

    static member private mkt_bal_l n l (r : SetTree<'T>) =
        if SetTree.Height l = SetTree.Height r + 2u then
            match l with
            | Empty ->
                failwith "mkt_bal_l"
            | Node (ll, lr, ln, _) ->
                if SetTree.Height ll < SetTree.Height lr then
                    match lr with
                    | Empty ->
                        failwith "mkt_bal_l"
                    | Node (lrl, lrr, lrn, _) ->
                        SetTree.Create lrn (SetTree.Create ln ll lrl) (SetTree.Create n lrr r)
                else
                    SetTree.Create ln ll (SetTree.Create n lr r)
        else
            SetTree.Create n l r

    static member private mkt_bal_r n l (r : SetTree<'T>) =
        if SetTree.Height r = SetTree.Height l + 2u then
            match r with
            | Empty ->
                failwith "mkt_bal_r"
            | Node (rl, rr, rn, _) ->
                if SetTree.Height rr < SetTree.Height rl then
                    match rl with
                    | Empty ->
                        failwith "mkt_bal_r"
                    | Node (rll, rlr, rln, _) ->
                        SetTree.Create rln (SetTree.Create n l rll) (SetTree.Create rn rlr rr)
                else
                    SetTree.Create rn (SetTree.Create n l rl) rr
        else
            SetTree.Create n l r

    static member private DeleteMax (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the maximum value from an empty tree."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, (Node (_,_,_,_) as right), n, _) ->
            let na, r = SetTree.DeleteMax right
            na, SetTree.mkt_bal_l n l r

    static member private DeleteRoot (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "Cannot delete the root of an empty tree."
        | Node (Empty, r, _, _) -> r
        | Node ((Node (_,_,_,_) as left), Empty, _, _) ->
            left
        | Node ((Node (_,_,_,_) as left), (Node (_,_,_,_) as right), _, _) ->
            let new_n, l = SetTree.DeleteMax left
            SetTree.mkt_bal_r new_n l right

    /// Determines if a SetTree contains a specified value.
    static member Contains value (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            false
        | Node (l, r, n, _) ->
            let comparison = compare value n
            if comparison = 0 then      // value = n
                true
            elif comparison < 0 then    // value < n
                SetTree.Contains value l
            else                        // value > n
                SetTree.Contains value r

    /// Removes the specified value from the tree.
    /// If the tree doesn't contain the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Delete x (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            Empty
        | Node (l, r, n, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then              // x = n
                SetTree.DeleteRoot tree
            elif comparison < 0 then            // x < n
                let la = SetTree.Delete x l
                SetTree.mkt_bal_r n la r
            else                                // x > n
                let a = SetTree.Delete x r
                SetTree.mkt_bal_l n l a

    /// Adds a value to a SetTree.
    /// If the tree already contains the value, no exception is thrown;
    /// the tree will be returned without modification.
    static member Insert x (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            Node (Empty, Empty, x, 1u)
        | Node (l, r, n, _) as tree ->
            let comparison = compare x n
            if comparison = 0 then                              // x = n
                tree
            elif comparison < 0 then                            // x < n
                SetTree.mkt_bal_l n (SetTree.Insert x l) r
            else                                                // x > n
                SetTree.mkt_bal_r n l (SetTree.Insert x r)

    /// Gets the maximum (greatest) value stored in the SetTree.
    static member MaxElement (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (_, Empty, n, _) ->
            n
        | Node (_, (Node (_,_,_,_) as right), _, _) ->
            SetTree.MaxElement right

    /// Gets the minimum (least) value stored in the SetTree.
    static member MinElement (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, _, n, _) ->
            n
        | Node ((Node (_,_,_,_) as left), _, _, _) ->
            SetTree.MinElement left

    /// Extracts the minimum (least) value from a SetTree,
    /// returning the value along with the updated tree.
    static member ExtractMin (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (Empty, r, n, _) ->
            n, r
        | Node (Node (left, mid, a, _), r, x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the minimum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = SetTree.Create x mid r
            SetTree.Create a left n
            |> SetTree.ExtractMin

    /// Extracts the minimum (least) value from a SetTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryExtractMin (tree : SetTree<'T>) =
        // Is the tree empty?
        if SetTree.IsEmptyTree tree then
            None, tree
        else
            let minElement, tree = SetTree.ExtractMin tree
            Some minElement, tree

    /// Extracts the maximum (greatest) value from a SetTree,
    /// returning the value along with the updated tree.
    static member ExtractMax (tree : SetTree<'T>) =
        match tree with
        | Empty ->
            invalidArg "tree" "The tree is empty."
        | Node (l, Empty, n, _) ->
            n, l
        | Node (l, Node (mid, right, a, _), x, _) ->
            // Rebalance the tree at the same time we're traversing downwards
            // to find the maximum value. This avoids the need to perform a
            // second traversal to remove the element once it's found.
            let n = SetTree.Create x l mid
            SetTree.Create a n right
            |> SetTree.ExtractMax

    /// Extracts the maximum (greatest) value from a SetTree,
    /// returning the value along with the updated tree.
    /// No exception is thrown if the tree is empty.
    static member TryExtractMax (tree : SetTree<'T>) =
        // Is the tree empty?
        if SetTree.IsEmptyTree tree then
            None, tree
        else
            let maxElement, tree = SetTree.ExtractMax tree
            Some maxElement, tree

    /// Counts the number of elements in the tree.
    static member Count (tree : SetTree<'T>) =
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
    static member Iter (action : 'T -> unit) (tree : SetTree<'T>) : unit =
        match tree with
        | Empty -> ()
        | Node (Empty, Empty, x, _) ->
            // Invoke the action with this single element.
            action x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| SetTree.Singleton x
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the action function.
                    action x

                | Node (Empty, z, x, _) ->
                    // Apply this value to the action function.
                    action x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| SetTree.Singleton x
                    stack.Push l

    /// Applies the given accumulating function to all elements in a SetTree.
    static member Fold (folder : 'State -> 'T -> 'State) (state : 'State) (tree : SetTree<'T>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, x, _) ->
            // Invoke the folder function on this single element and return the result.
            folder state x
        | Node (l, r, x, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| SetTree.Singleton x
            stack.Push l

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, x)

                | Node (Empty, z, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (state, x)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| SetTree.Singleton x
                    stack.Push l

            // Return the final state value.
            state

    /// Applies the given accumulating function to all elements in a SetTree.
    static member FoldBack (folder : 'T -> 'State -> 'State) (state : 'State) (tree : SetTree<'T>) =
        match tree with
        | Empty -> state
        | Node (Empty, Empty, x, _) ->
            // Invoke the folder function on this single element and return the result.
            folder x state
        | Node (l, r, x, _) ->
            // Adapt the folder function since we'll always supply all of the arguments at once.
            let folder = FSharpFunc<_,_,_>.Adapt folder

            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// The current state value.
            let mutable state = state

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push l
            stack.Push <| SetTree.Singleton x
            stack.Push r

            while stack.Count > 0 do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (x, state)

                | Node (z, Empty, x, _) ->
                    // Apply this value to the folder function.
                    state <- folder.Invoke (x, state)

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push l
                    stack.Push <| SetTree.Singleton x
                    stack.Push r

            // Return the final state value.
            state

    //
    static member Exists (predicate : 'T -> bool) (tree : SetTree<'T>) : bool =
        match tree with
        | Empty -> false
        | Node (Empty, Empty, x, _) ->
            // Apply the predicate function to this element and return the result.
            predicate x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have we found a matching element?
            let mutable foundMatch = false

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| SetTree.Singleton x
            stack.Push l

            while stack.Count > 0 && not foundMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate x

                | Node (Empty, z, x, _) ->
                    // Apply the predicate to this element.
                    foundMatch <- predicate x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| SetTree.Singleton x
                    stack.Push l

            // Return the value indicating whether or not a matching element was found.
            foundMatch

    //
    static member Forall (predicate : 'T -> bool) (tree : SetTree<'T>) : bool =
        match tree with
        | Empty -> true
        | Node (Empty, Empty, x, _) ->
            // Apply the predicate function to this element and return the result.
            predicate x
        | Node (l, r, x, _) ->
            /// Mutable stack. Holds the trees which still need to be traversed.
            let stack = Stack (defaultStackCapacity)

            /// Have all of the elements we've seen so far matched the predicate?
            let mutable allElementsMatch = true

            // Traverse the tree using the mutable stack, applying the folder function to
            // each value to update the state value.
            stack.Push r
            stack.Push <| SetTree.Singleton x
            stack.Push l

            while stack.Count > 0 && allElementsMatch do
                match stack.Pop () with
                | Empty -> ()
                | Node (Empty, Empty, x, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate x

                | Node (Empty, z, x, _) ->
                    // Apply the predicate to this element.
                    allElementsMatch <- predicate x

                    // Push the non-empty child onto the stack.
                    stack.Push z

                | Node (l, r, x, _) ->
                    // Push the children onto the stack.
                    // Also push a new Node onto the stack which contains the value from
                    // this Node, so it'll be processed in the correct order.
                    stack.Push r
                    stack.Push <| SetTree.Singleton x
                    stack.Push l

            // Return the value indicating if all elements matched the predicate.
            allElementsMatch

    /// Builds a new SetTree from the elements of a sequence.
    static member OfSeq (sequence : seq<_>) : SetTree<'T> =
        (Empty, sequence)
        ||> Seq.fold (fun tree el ->
            SetTree.Insert el tree)

    /// Builds a new SetTree from the elements of an list.
    static member OfList (list : _ list) : SetTree<'T> =
        (Empty, list)
        ||> List.fold (fun tree el ->
            SetTree.Insert el tree)

    /// Builds a new SetTree from the elements of an array.
    static member OfArray (array : _[]) : SetTree<'T> =
        (Empty, array)
        ||> Array.fold (fun tree el ->
            SetTree.Insert el tree)

    /// Returns a sequence containing the elements stored
    /// in a SetTree, ordered from least to greatest.
    static member ToSeq (tree : SetTree<'T>) =
        seq {
        match tree with
        | Empty -> ()
        | Node (l, r, n, _) ->
            yield! SetTree.ToSeq l
            yield n
            yield! SetTree.ToSeq r
        }

    /// Returns a list containing the elements stored in
    /// a SetTree, ordered from least to greatest. 
    static member ToList (tree : SetTree<'T>) =
        ([], tree)
        ||> SetTree.FoldBack (fun el lst ->
            el :: lst)

    /// Returns an array containing the elements stored in
    /// a SetTree, ordered from least to greatest.
    static member ToArray (tree : SetTree<'T>) =
        let elements = ResizeArray ()
        SetTree.Iter elements.Add tree
        elements.ToArray ()

    /// Computes the union of two SetTrees.
    static member Union (tree1 : SetTree<'T>, tree2 : SetTree<'T>) : SetTree<'T> =
        (* OPTIMIZE :   This function should be re-implemented to use the linear-time
                        algorithm which traverses both trees simultaneously and merges
                        them in a single pass. *)

        // Guess which tree is larger (contains a greater number of elements) based on
        // the height of the trees; then, merge the smaller tree into the larger tree.
        if SetTree.Height tree1 < SetTree.Height tree2 then
            // tree1 smaller than tree2
            SetTree.FoldBack SetTree.Insert tree2 tree1
        else
            SetTree.FoldBack SetTree.Insert tree1 tree2

    /// Computes the intersection of two SetTrees.
    static member Intersect (tree1 : SetTree<'T>, tree2 : SetTree<'T>) : SetTree<'T> =
        (* OPTIMIZE :   This function should be re-implemented to use the linear-time
                        algorithm which traverses both trees simultaneously and merges
                        them in a single pass. *)

        // Guess which tree is larger (contains a greater number of elements) based on
        // the height of the trees; then, fold over the larger tree, removing it's
        // elements from the smaller tree. This minimizes the overhead due to rebalancing.
        if SetTree.Height tree1 < SetTree.Height tree2 then
            // Fold over the smaller tree, removing any elements which
            // are not also in the larger tree.
            (tree1, tree1)
            ||> SetTree.Fold (fun tree1 el ->
                if SetTree.Contains el tree2 then tree1
                else SetTree.Delete el tree1)
        else
            // Fold over the smaller tree, removing any elements which
            // are not also in the larger tree.
            (tree2, tree2)
            ||> SetTree.Fold (fun tree2 el ->
                if SetTree.Contains el tree1 then tree2
                else SetTree.Delete el tree2)

    /// Returns a new SetTree created by removing the elements of the
    /// second SetTree from the first.
    static member Difference (tree1 : SetTree<'T>, tree2 : SetTree<'T>) : SetTree<'T> =
        (* OPTIMIZE :   This function should be re-implemented to use the linear-time
                        algorithm which traverses both trees simultaneously and merges
                        them in a single pass. *)

        // Fold over tree2, removing it's elements from tree1
        SetTree.FoldBack SetTree.Delete tree1 tree2

    //
    static member IsSubset (a : SetTree<'T>, b : SetTree<'T>) : bool =
        SetTree.Forall (fun x -> SetTree.Contains x b) a

    //
    static member IsProperSubset (a : SetTree<'T>, b : SetTree<'T>) : bool =
        SetTree.Forall (fun x -> SetTree.Contains x b) a
        && SetTree.Exists (fun x -> not (SetTree.Contains x a)) b

    static member private CompareStacks (l1 : SetTree<'T> list) (l2 : SetTree<'T> list) : int =
        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | (Empty :: t1),(Empty :: t2) ->
            SetTree.CompareStacks t1 t2
        | (Node (Empty, Empty, n1k, _) :: t1), (Node (Empty, Empty, n2k, _) :: t2) ->
            let c = compare n1k n2k
            if c <> 0 then c
            else SetTree.CompareStacks t1 t2

        | (Node (Empty, Empty, n1k, _) :: t1), (Node (Empty, n2r, n2k, _) :: t2) ->
            let c = compare n1k n2k
            if c <> 0 then c
            else SetTree.CompareStacks (Empty :: t1) (n2r :: t2)

        | (Node ((Empty as emp), n1r, n1k, _) :: t1), (Node (Empty, Empty, n2k, _) :: t2) ->
            let c = compare n1k n2k
            if c <> 0 then c
            else SetTree.CompareStacks (n1r :: t1) (emp :: t2)

        | (Node (Empty, n1r, n1k, _) :: t1), (Node (Empty, n2r, n2k, _) :: t2) ->
            let c = compare n1k n2k
            if c <> 0 then c
            else SetTree.CompareStacks (n1r :: t1) (n2r :: t2)

        | ((Node (Empty, Empty, n1k, _) :: t1) as l1), _ ->
            SetTree.CompareStacks (Empty :: l1) l2
        
        | (Node (n1l, n1r, n1k, _) :: t1), _ ->
            SetTree.CompareStacks (n1l :: Node (Empty, n1r, n1k, 0u) :: t1) l2
        
        | _, ((Node (Empty, Empty, n2k, _) :: t2) as l2) ->
            SetTree.CompareStacks l1 (Empty :: l2)
        
        | _, (Node (n2l, n2r, n2k, _) :: t2) ->
            SetTree.CompareStacks l1 (n2l :: Node (Empty, n2r, n2k, 0u) :: t2)
                
    static member Compare (s1 : SetTree<'T>, s2 : SetTree<'T>) : int =
        match s1, s2 with
        | Empty, Empty -> 0
        | Empty, _ -> -1
        | _, Empty -> 1
        | _ ->
            SetTree<'T>.CompareStacks [s1] [s2]

(*** Imperative left-to-right iterators. ***)

[<NoEquality; NoComparison>]
type internal SetIterator<'T> when 'T : comparison  = 
    { mutable stack: SetTree<'T> list;  // invariant: always collapseLHS result 
        mutable started : bool           // true when MoveNext has been called   
    }

[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module internal SetIterator =
    open System.Collections
    open System.Collections.Generic

    // collapseLHS:
    // a) Always returns either [] or a list starting with SetOne.
    // b) The "fringe" of the set stack is unchanged.
    let rec collapseLHS stack =
        match stack with
        | [] -> []
        | Empty :: rest ->
            collapseLHS rest
        | Node (Empty, Empty, _, _) :: _ ->
            stack
        | Node (l,r,k,_) :: rest ->
            collapseLHS (l :: (Node (Empty, Empty, k, 0u)) :: r :: rest)
          
    let mkIterator s = {
        stack = collapseLHS [s];
        started = false; }

    let notStarted () =
        //raise (new System.InvalidOperationException(SR.GetString(SR.enumerationNotStarted)))
        invalidOp "enumerationNotStarted"
    let alreadyFinished () =
        //raise (new System.InvalidOperationException(SR.GetString(SR.enumerationAlreadyFinished)))
        invalidOp "enumerationAlreadyFinished"

    let current i =
        if i.started then
            match i.stack with
            | Node (Empty, Empty, k, _) :: _ -> k
            | [] -> alreadyFinished ()
            | _ -> failwith "Please report error: Set iterator, unexpected stack for current"
        else
            notStarted ()

    let rec moveNext i =
        if i.started then
            match i.stack with
            | Node (Empty, Empty, _, _) :: rest ->
                i.stack <- collapseLHS rest
                not i.stack.IsEmpty
            | [] -> false
            | _ -> failwith "Please report error: Set iterator, unexpected stack for moveNext"
        else
            i.started <- true       // The first call to MoveNext "starts" the enumeration.
            not i.stack.IsEmpty

    let mkIEnumerator s =
        let i = ref (mkIterator s)
        { new IEnumerator<_> with
                member __.Current = current !i
            interface IEnumerator with
                member __.Current = box (current !i)
                member __.MoveNext () = moveNext !i
                member __.Reset () = i := mkIterator s
            interface System.IDisposable with
                member __.Dispose () = () }


//
[<Sealed; CompiledName("FSharpSet`1")>]
#if FX_NO_DEBUG_PROXIES
#else
[<DebuggerTypeProxy(typedefof<SetDebugView<_>>)>]
#endif
#if FX_NO_DEBUG_DISPLAYS
#else
[<DebuggerDisplay("Count = {Count}")>]
#endif
[<CodeAnalysis.SuppressMessage("Microsoft.Naming", "CA1710:IdentifiersShouldHaveCorrectSuffix")>]
type Set<[<EqualityConditionalOn>] 'T when 'T : comparison> private (tree : SetTree<'T>) =
    /// The empty set instance.
    static let empty : Set<'T> = Set Empty

    /// The empty set instance.
    static member internal Empty =
        empty

    //
    new (elements : seq<'T>) =
        // Preconditions
        // TODO : Check for null input.

        Set (SetTree.OfSeq elements)

    //
    member private __.Tree
        with get () = tree

    //
    member __.Count
        with get () =
            int <| SetTree.Count tree

    //
    member __.IsEmpty
        with get () =
            match tree with
            | Empty -> true
            | Node (_,_,_,_) -> false

    //
    member __.MinimumElement
        with get () =
            SetTree.MinElement tree

    //
    member __.MaximumElement
        with get () =
            SetTree.MaxElement tree

    //
    member __.Contains (value : 'T) : bool =
        SetTree.Contains value tree

    //
    member this.Add (value : 'T) : Set<'T> =
        // Add the element to the SetTree; if the result is the same (i.e., the tree
        // already contained the element), return this set instead of creating a new one.
        let tree' = SetTree.Insert value tree
        if System.Object.ReferenceEquals (tree, tree') then this
        else Set (tree')

    //
    member this.Remove (value : 'T) : Set<'T> =
        // Remove the element from the SetTree; if the result is the same (i.e., the tree
        // did not contain the element), return this set instead of creating a new one.
        let tree' = SetTree.Delete value tree
        if System.Object.ReferenceEquals (tree, tree') then this
        else Set (tree')

    //
    static member internal Singleton (value : 'T) : Set<'T> =
        Set (SetTree.Singleton value)

    //
    static member internal Union (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        // Compute the union of the trees.
        // If the result is the same as either tree (i.e., one set was a subset of the other)
        // return that tree's corresponding set instead of creating a new one.
        let result = SetTree.Union (set1.Tree, set2.Tree)
        if System.Object.ReferenceEquals (set1.Tree, result) then set1
        elif System.Object.ReferenceEquals (set2.Tree, result) then set2
        else Set (result)

    //
    static member internal Intersection (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        // Compute the intersection of the trees.
        // If the result is the same as either tree (i.e., one set was a subset of the other)
        // return that tree's corresponding set instead of creating a new one.
        let result = SetTree.Intersect (set1.Tree, set2.Tree)
        if System.Object.ReferenceEquals (set1.Tree, result) then set1
        elif System.Object.ReferenceEquals (set2.Tree, result) then set2
        else Set (result)

    //
    static member internal Difference (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        // Remove the elements in set2 from set1.
        // If the result is the same as set1's tree (i.e., set2 did not contain any elements
        // from set1), return set1 instead of creating a new set.
        let result = SetTree.Difference (set1.Tree, set2.Tree)
        if System.Object.ReferenceEquals (set1.Tree, result) then set1
        else Set (result)

    //
    static member internal UnionMany (sets : seq<Set<'T>>) : Set<'T> =
        // Preconditions
        // TODO : Check input for null.

        let combinedSetTree =
            (SetTree.Empty, sets)
            ||> Seq.fold (fun combinedSetTree set ->
                SetTree.Union (combinedSetTree, set.Tree))

        Set (combinedSetTree)

    //
    static member internal IntersectMany (sets : seq<Set<'T>>) : Set<'T> =
        Seq.reduce (fun s1 s2 -> Set<_>.Intersection(s1,s2)) sets

    //
    static member internal FromSeq (sequence : seq<'T>) : Set<'T> =
        // Preconditions
        // TODO

        Set (SetTree.OfSeq sequence)

    //
    static member internal FromList (list : 'T list) : Set<'T> =
        // Preconditions
        // TODO

        Set (SetTree.OfList list)

    //
    static member internal FromArray (arr : 'T[]) : Set<'T> =
        // Preconditions
        // TODO

        Set (SetTree.OfArray arr)

    //
    member internal __.ToSeq () =
        SetTree.ToSeq tree

    //
    member internal __.ToList () =
        SetTree.ToList tree

    //
    member internal __.ToArray () =
        SetTree.ToArray tree

    //
    static member op_Addition (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        Set<'T>.Union (set1, set2)

    //
    static member op_Subtraction (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        Set<'T>.Difference (set1, set2)

    //
    member __.IsSubsetOf (otherSet : Set<'T>) : bool =
        SetTree.IsSubset (tree, otherSet.Tree)

    //
    member __.IsProperSubsetOf (otherSet : Set<'T>) : bool =
        SetTree.IsProperSubset (tree, otherSet.Tree)

    //
    member __.IsSupersetOf (otherSet : Set<'T>) : bool =
        SetTree.IsSubset (otherSet.Tree, tree)

    //
    member __.IsProperSupersetOf (otherSet : Set<'T>) : bool =
        SetTree.IsProperSubset (otherSet.Tree, tree)

    //
    member internal __.Iterate (action : 'T -> unit) : unit =
        SetTree.Iter action tree

    //
    member internal __.Exists (predicate : 'T -> bool) : bool =
        SetTree.Exists predicate tree

    //
    member internal __.ForAll (predicate : 'T -> bool) : bool =
        SetTree.Forall predicate tree

    //
    member internal __.Fold (folder : 'State -> 'T -> 'State) (state : 'State) : 'State =
        SetTree.Fold folder state tree

    //
    member internal __.FoldBack (folder : 'T -> 'State -> 'State) (state : 'State) : 'State =
        SetTree.FoldBack folder state tree

    //
    member internal __.Map (mapping : 'T -> 'U) : Set<'U> =
        let mappedTree =
            (SetTree.Empty, tree)
            ||> SetTree.Fold (fun mappedTree el ->
                SetTree.Insert (mapping el) mappedTree)

        Set (mappedTree)

    //
    member internal __.Filter (predicate : 'T -> bool) : Set<'T> =
        let filteredTree =
            (tree, tree)
            ||> SetTree.Fold (fun filteredTree el ->
                if predicate el then filteredTree
                else SetTree.Delete el filteredTree)

        Set (filteredTree)

    //
    member internal this.Partition (predicate : 'T -> bool) : Set<'T> * Set<'T> =
        let trueTree, falseTree =
            ((tree, tree), tree)
            ||> SetTree.Fold (fun (trueTree, falseTree) el ->
                if predicate el then
                    trueTree,
                    SetTree.Delete el falseTree
                else
                    SetTree.Delete el trueTree,
                    falseTree)

        // If either of the 'true' or 'false' trees are equivalent to the input tree,
        // return this set as one component of the returned tuple -- this avoids creating
        // an additional set for no reason.
        if System.Object.ReferenceEquals (tree, trueTree) then
            this, empty
        elif System.Object.ReferenceEquals (tree, falseTree) then
            empty, this
        else
            Set (trueTree), Set (falseTree)

    // OPTIMIZE : Instead of computing this repeatedly -- this type is immutable so we should
    // lazily compute the hashcode once instead; however, we do need to account for the case
    // where an instance is created via deserialization, so it may make sense to use a 'ref'
    // field (which is excluded from serialization) with Interlocked.Exchange instead of using
    // a 'lazy' value.
    member __.ComputeHashCode () =
        let inline combineHash x y = (x <<< 1) + y + 631
        (0, tree)
        ||> SetTree.Fold (fun res x ->
            combineHash res (hash x))
        |> abs

    override this.GetHashCode () =
        this.ComputeHashCode ()

    // OPTIMIZE : Would it be significantly faster if we re-implemented this to work
    // directly on the SetTrees instead of using enumerators? Or, at least using an
    // imperative loop instead of a recursive function?
    override this.Equals other =
        match other with
        | :? Set<'T> as other ->
            use e1 = (this :> seq<_>).GetEnumerator ()
            use e2 = (other :> seq<_>).GetEnumerator ()
            let rec loop () =
                let m1 = e1.MoveNext ()
                let m2 = e2.MoveNext ()
                (m1 = m2) && (not m1 || ((e1.Current = e2.Current) && loop ()))
            loop ()
        | _ -> false

    override x.ToString () =
        match List.ofSeq (Seq.truncate 4 x) with
        | [] -> "set []"
        | [h1] ->
            System.Text.StringBuilder()
                .Append("set [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("]")
                .ToString()
        | [h1; h2] ->
            System.Text.StringBuilder()
                .Append("set [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("]")
                .ToString()
        | [h1; h2; h3] ->
            System.Text.StringBuilder()
                .Append("set [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h3)
                .Append("]")
                .ToString()
        | h1 :: h2 :: h3 :: _ ->
            System.Text.StringBuilder()
                .Append("set [")
                .Append(LanguagePrimitives.anyToStringShowingNull h1)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h2)
                .Append("; ")
                .Append(LanguagePrimitives.anyToStringShowingNull h3)
                .Append("; ... ]")
                .ToString()

    interface System.IComparable with
        /// <inherit />
        member __.CompareTo other =
            SetTree.Compare (tree, (other :?> Set<'T>).Tree)

    interface System.Collections.IEnumerable with
        /// <inherit />
        member __.GetEnumerator () =
//            (SetTree.ToSeq tree).GetEnumerator ()
            SetIterator.mkIEnumerator tree
            :> System.Collections.IEnumerator

    interface IEnumerable<'T> with
        /// <inherit />
        member __.GetEnumerator () =
            //(SetTree.ToSeq tree).GetEnumerator ()
            SetIterator.mkIEnumerator tree

    interface ICollection<'T> with
        /// <inherit />
        member __.Count
            with get () =
                int <| SetTree.Count tree

        /// <inherit />
        member __.IsReadOnly
            with get () = true

        /// <inherit />
        member __.Add x =
            raise <| System.NotSupportedException "Sets cannot be mutated."

        /// <inherit />
        member __.Clear () =
            raise <| System.NotSupportedException "Sets cannot be mutated."

        /// <inherit />
        member __.Contains (item : 'T) =
            SetTree.Contains item tree

        /// <inherit />
        member this.CopyTo (array, arrayIndex) =
            // Preconditions
            if System.Object.ReferenceEquals (null, array) then
                nullArg "array"
            elif arrayIndex < 0 then
                raise <| System.ArgumentOutOfRangeException "arrayIndex"

            let count = int <| SetTree.Count tree
            if arrayIndex + count > Array.length array then
                invalidArg "arrayIndex"
                    "There is not enough room in the array to copy the elements when starting at the specified index."

            this.Fold (fun index el ->
                array.[index] <- el
                index + 1) arrayIndex
            |> ignore

        /// <inherit />
        member __.Remove item : bool =
            raise <| System.NotSupportedException "Sets cannot be mutated."

and [<Sealed>]
    internal SetDebugView<'T when 'T : comparison> (set : Set<'T>) =

#if FX_NO_DEBUG_DISPLAYS
#else
    [<DebuggerBrowsable(DebuggerBrowsableState.RootHidden)>]
#endif
    member __.Items
        with get () : 'T[] =
            set.ToArray ()

//
[<RequireQualifiedAccess; CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Set =
    [<CompiledName("IsEmpty")>]
    let (*inline*) isEmpty (s : Set<'T>) = s.IsEmpty

    [<CompiledName("Contains")>]
    let (*inline*) contains x (s : Set<'T>) = s.Contains(x)

    [<CompiledName("Add")>]
    let (*inline*) add x (s : Set<'T>) = s.Add(x)

    [<CompiledName("Singleton")>]
    let singleton x = Set<'T>.Singleton(x)

    [<CompiledName("Remove")>]
    let (*inline*) remove x (s : Set<'T>) = s.Remove(x)

    [<CompiledName("Union")>]
    let (*inline*) union (s1 : Set<'T>) (s2 : Set<'T>) = s1 + s2

    [<CompiledName("UnionMany")>]
    let unionMany sets = Set<_>.UnionMany(sets)

    [<CompiledName("Intersect")>]
    let intersect (s1 : Set<'T>) (s2 : Set<'T>) = Set<'T>.Intersection(s1,s2)

    [<CompiledName("IntersectMany")>]
    let intersectMany sets = Set<_>.IntersectMany(sets)

    [<CompiledName("Iterate")>]
    let iter f (s : Set<'T>) = s.Iterate(f)

    [<GeneralizableValue>]
    [<CompiledName("Empty")>]
    let empty<'T when 'T : comparison> : Set<'T> = Set<'T>.Empty

    [<CompiledName("ForAll")>]
    let forall f (s : Set<'T>) = s.ForAll f

    [<CompiledName("Exists")>]
    let exists f (s : Set<'T>) = s.Exists f

    [<CompiledName("Filter")>]
    let filter f (s : Set<'T>) = s.Filter f

    [<CompiledName("Partition")>]
    let partition f (s : Set<'T>) = s.Partition f 

    [<CompiledName("Fold")>]
    let fold<'T, 'State when 'T : comparison> f (z : 'State) (s : Set<'T>) = s.Fold f z

    [<CompiledName("FoldBack")>]
    let foldBack<'T, 'State when 'T : comparison> f (s : Set<'T>) (z : 'State) = s.FoldBack f z

    [<CompiledName("Map")>]
    let map f (s : Set<'T>) = s.Map f

    [<CompiledName("Count")>]
    let count (s : Set<'T>) = s.Count

    [<CompiledName("MinumumElement")>]
    let minimumElement (s : Set<'T>) = s.MinimumElement

    [<CompiledName("MaximumElement")>]
    let maximumElement (s : Set<'T>) = s.MaximumElement

    [<CompiledName("OfList")>]
    let ofList l = Set<_>.FromList l

    [<CompiledName("OfArray")>]
    let ofArray (l : 'T array) = Set<'T>.FromArray l

    [<CompiledName("ToList")>]
    let toList (s : Set<'T>) = s.ToList()
 
    [<CompiledName("ToArray")>]
    let toArray (s : Set<'T>) = s.ToArray()

    [<CompiledName("ToSeq")>]
    let toSeq (s : Set<'T>) : seq<'T> =
        //s.ToSeq ()
        (s :> seq<_>)

    [<CompiledName("OfSeq")>]
    let ofSeq (c : seq<_>) = Set<_>.FromSeq c

    [<CompiledName("Difference")>]
    let (*inline*) difference (s1: Set<'T>) (s2: Set<'T>) = s1 - s2

    [<CompiledName("IsSubset")>]
    let (*inline*) isSubset (x:Set<'T>) (y: Set<'T>) =
        x.IsSubsetOf y

    [<CompiledName("IsSuperset")>]
    let (*inline*) isSuperset (x:Set<'T>) (y: Set<'T>) =
        x.IsSupersetOf y

    [<CompiledName("IsProperSubset")>]
    let (*inline*) isProperSubset (x:Set<'T>) (y: Set<'T>) =
        x.IsProperSubsetOf y

    [<CompiledName("IsProperSuperset")>]
    let (*inline*) isProperSuperset (x:Set<'T>) (y: Set<'T>) =
        x.IsProperSupersetOf y

    [<CompiledName("MinElement")>]
    let (*inline*) minElement (s : Set<'T>) = s.MinimumElement

    [<CompiledName("MaxElement")>]
    let (*inline*) maxElement (s : Set<'T>) = s.MaximumElement

