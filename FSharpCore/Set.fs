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
type (*internal*) SetTree<'T when 'T : comparison> =
    /// Empty tree.
    | Empty
    /// Node.
    // Left-Child, Right-Child, Value, Height
    | Node of SetTree<'T> * SetTree<'T> * 'T * uint32

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
        raise <| System.NotImplementedException "SetTree.Union"

    /// Computes the intersection of two SetTrees.
    static member Intersect (tree1 : SetTree<'T>, tree2 : SetTree<'T>) : SetTree<'T> =
        raise <| System.NotImplementedException "SetTree.Intersect"

    /// Returns a new SetTree created by removing the elements of the
    /// second SetTree from the first.
    static member Difference (tree1 : SetTree<'T>, tree2 : SetTree<'T>) : SetTree<'T> =
        raise <| System.NotImplementedException "SetTree.Difference"

(*
    /// Implementation. Returns the height of a SetTree.
    // OPTIMIZE : This should be re-implemented without continuations --
    // move it into 'ComputeHeight' and use a mutable stack to traverse the tree.
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
    static member ComputeHeight (tree : SetTree<'T>) =
        SetTree.ComputeHeightRec tree id
        
    /// Determines if a SetTree is correctly formed.
    /// It isn't necessary to call this at run-time, though it may be useful for asserting
    /// the correctness of functions which weren't extracted from the Isabelle theory.
    static member AvlInvariant (tree : SetTree<'T>) =
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
*)

//
[<Sealed; CompiledName("FSharpSet`1")>]
type Set<[<EqualityConditionalOn>] 'T when 'T : comparison> private (tree : SetTree<'T>) =
    /// The empty set instance.
    static let empty = Set Empty

    /// The empty set instance.
    static member internal Empty =
        empty

    //
    member private __.Tree
        with get () = tree

    //
    member __.Count
        with get () =
            SetTree.Count tree

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
    static member op_Addition (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        Set<'T>.Union (set1, set2)

    //
    static member op_Subtraction (set1 : Set<'T>, set2 : Set<'T>) : Set<'T> =
        Set<'T>.Difference (set1, set2)

    //
    member __.IsSubsetOf (otherSet : Set<'T>) : bool =
        raise <| System.NotImplementedException "Set.IsSubsetOf"

    //
    member __.IsProperSubsetOf (otherSet : Set<'T>) : bool =
        raise <| System.NotImplementedException "Set.IsProperSubsetOf"

    //
    member __.IsSupersetOf (otherSet : Set<'T>) : bool =
        raise <| System.NotImplementedException "Set.IsSupersetOf"

    //
    member __.IsProperSupersetOf (otherSet : Set<'T>) : bool =
        raise <| System.NotImplementedException "Set.IsProperSupersetOf"

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
        raise <| System.NotImplementedException "Set.UnionMany"

    //
    static member internal IntersectMany (sets : seq<Set<'T>>) : Set<'T> =
        raise <| System.NotImplementedException "Set.IntersectMany"

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
    let intersect (s1 : Set<'T>)  (s2 : Set<'T>)  = Set<'T>.Intersection(s1,s2)

    [<CompiledName("IntersectMany")>]
    let intersectMany sets  = Set<_>.IntersectMany(sets)

//    [<CompiledName("Iterate")>]
//    let iter f (s : Set<'T>)  = s.Iterate(f)

//    [<CompiledName("Empty")>]
//    let empty<'T when 'T : comparison> : Set<'T> = Set<'T>.Empty

//    [<CompiledName("ForAll")>]
//    let forall f (s : Set<'T>) = s.ForAll f
//
//    [<CompiledName("Exists")>]
//    let exists f (s : Set<'T>) = s.Exists f
//
//    [<CompiledName("Filter")>]
//    let filter f (s : Set<'T>) = s.Filter f
//
//    [<CompiledName("Partition")>]
//    let partition f (s : Set<'T>) = s.Partition f 
//
//    [<CompiledName("Fold")>]
//    let fold<'T,'State  when 'T : comparison> f (z:'State) (s : Set<'T>) = SetTree.fold f z s.Tree
//
//    [<CompiledName("FoldBack")>]
//    let foldBack<'T,'State when 'T : comparison> f (s : Set<'T>) (z:'State) = SetTree.foldBack f s.Tree z
//
//    [<CompiledName("Map")>]
//    let map f (s : Set<'T>) = s.Map f

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
        s.ToSeq ()

    [<CompiledName("OfSeq")>]
    let ofSeq (c : seq<_>) = Set<_>.FromSeq c

    [<CompiledName("Difference")>]
    let (*inline*) difference (s1: Set<'T>) (s2: Set<'T>) = s1 - s2

//    [<CompiledName("IsSubset")>]
//    let isSubset (x:Set<'T>) (y: Set<'T>) = SetTree.subset x.Comparer x.Tree y.Tree 
//
//    [<CompiledName("IsSuperset")>]
//    let isSuperset (x:Set<'T>) (y: Set<'T>) = SetTree.subset x.Comparer y.Tree x.Tree
//
//    [<CompiledName("IsProperSubset")>]
//    let isProperSubset (x:Set<'T>) (y: Set<'T>) = SetTree.psubset x.Comparer x.Tree y.Tree 
//
//    [<CompiledName("IsProperSuperset")>]
//    let isProperSuperset (x:Set<'T>) (y: Set<'T>) = SetTree.psubset x.Comparer y.Tree x.Tree

    [<CompiledName("MinElement")>]
    let (*inline*) minElement (s : Set<'T>) = s.MinimumElement

    [<CompiledName("MaxElement")>]
    let (*inline*) maxElement (s : Set<'T>) = s.MaximumElement


    

