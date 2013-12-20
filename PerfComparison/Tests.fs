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

namespace PerfComparison.Tests

open System.Collections.Immutable
open System.Diagnostics
open PerfComparison


//
type TestResult<'T when 'T : comparison> = {
    ``FSharp.Core (Original)`` : 'T;
    ``FSharp.Core (Optimized)`` : 'T;
    ``ExtCore (Patricia Trie)`` : 'T;
    ``ExtCore (HashSet)`` : 'T;
    ``System.Collections.Immutable.ImmutableHashSet`` : 'T
    ``System.Collections.Immutable.ImmutableSortedSet`` : 'T
} with
    /// Print timing results.
    static member PrintTimings (result : TestResult<System.TimeSpan>) =
        printfn "FSharp.Core (Original)  : %4f (ms)" result.``FSharp.Core (Original)``.TotalMilliseconds
        printfn "FSharp.Core (Optimized) : %4f (ms)" result.``FSharp.Core (Optimized)``.TotalMilliseconds
        printfn "ExtCore (Patricia Trie) : %4f (ms)" result.``ExtCore (Patricia Trie)``.TotalMilliseconds
        printfn "ExtCore (HashSet)       : %4f (ms)" result.``ExtCore (HashSet)``.TotalMilliseconds
        printfn "ImmutableHashSet        : %4f (ms)" result.``System.Collections.Immutable.ImmutableHashSet``.TotalMilliseconds
        printfn "ImmutableSortedSet      : %4f (ms)" result.``System.Collections.Immutable.ImmutableSortedSet``.TotalMilliseconds
        printfn ""


/// Functions for benchmarking set creation (and by correlation, the add/insert function).
module Create =
    //
    let int32 count maxValue density =
        let values = RandomArray.int32 count maxValue density
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.ofArray values
        watch.Stop ()
        let baselineTime = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.ofArray values
        watch.Stop ()
        let result1Time = watch.Elapsed
        
        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = IntSet.ofArray values
        watch.Stop ()
        let result2Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.ofArray values
        watch.Stop ()
        let result3Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 = ImmutableHashSet.Create<int> (values)
        watch.Stop ()
        let result4Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 = ImmutableSortedSet.Create<int> (values)
        watch.Stop ()
        let result5Time = watch.Elapsed

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }

    //
    let int64 count maxValue density =
        let values = RandomArray.int64 count maxValue density
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.ofArray values
        watch.Stop ()
        let baselineTime = watch.Elapsed
        
        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.ofArray values
        watch.Stop ()
        let result1Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = LongSet.ofArray values
        watch.Stop ()
        let result2Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.ofArray values
        watch.Stop ()
        let result3Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 = ImmutableHashSet.Create<int64> (values)
        watch.Stop ()
        let result4Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 = ImmutableSortedSet.Create<int64> (values)
        watch.Stop ()
        let result5Time = watch.Elapsed

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }


/// Functions for benchmarking the set union operation.
module Union =
    //
    let int32 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.unionMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.IntSet sets from the values.
        let intSets = Array.map IntSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = IntSet.unionMany intSets
        watch.Stop ()
        let result2Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.HashSet sets from the values.
        let hashSets = Array.map HashSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.unionMany hashSets
        watch.Stop ()
        let result3Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableHashSet sets from the values.
        let immutableHashSets =
            setValues |> Array.map (fun vals -> ImmutableHashSet.Create<int> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 =
            let mutable result = immutableHashSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Union immutableHashSets.[i]
            result
        watch.Stop ()
        let result4Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableSortedSet sets from the values.
        let immutableSortedSets =
            setValues |> Array.map (fun vals -> ImmutableSortedSet.Create<int> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 =
            let mutable result = immutableSortedSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Union immutableSortedSets.[i]
            result
        watch.Stop ()
        let result5Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = IntSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }

    //
    let int64 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.unionMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed

        // Create ExtCore.LongSet sets from the values.
        let longSets = Array.map LongSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = LongSet.unionMany longSets
        watch.Stop ()
        let result2Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.HashSet sets from the values.
        let hashSets = Array.map HashSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.unionMany hashSets
        watch.Stop ()
        let result3Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableHashSet sets from the values.
        let immutableHashSets =
            setValues |> Array.map (fun vals -> ImmutableHashSet.Create<int64> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 =
            let mutable result = immutableHashSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Union immutableHashSets.[i]
            result
        watch.Stop ()
        let result4Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableSortedSet sets from the values.
        let immutableSortedSets =
            setValues |> Array.map (fun vals -> ImmutableSortedSet.Create<int64> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 =
            let mutable result = immutableSortedSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Union immutableSortedSets.[i]
            result
        watch.Stop ()
        let result5Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = FSharpCore.Set.toArray result1)
        assert (Set.toArray baseline = LongSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }


/// Functions for benchmarking the set intersection operation.
module Intersect =
    //
    let int32 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.intersectMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.IntSet sets from the values.
        let intSets = Array.map IntSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = IntSet.intersectMany intSets
        watch.Stop ()
        let result2Time = watch.Elapsed

        // Create ExtCore.HashSet sets from the values.
        let hashSets = Array.map HashSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.intersectMany hashSets
        watch.Stop ()
        let result3Time = watch.Elapsed

        // Create System.Collections.Immutable.ImmutableHashSet sets from the values.
        let immutableHashSets =
            setValues |> Array.map (fun vals -> ImmutableHashSet.Create<int> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 =
            let mutable result = immutableHashSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Intersect immutableHashSets.[i]
            result
        watch.Stop ()
        let result4Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableSortedSet sets from the values.
        let immutableSortedSets =
            setValues |> Array.map (fun vals -> ImmutableSortedSet.Create<int> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 =
            let mutable result = immutableSortedSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Intersect immutableSortedSets.[i]
            result
        watch.Stop ()
        let result5Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = IntSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }

    //
    let int64 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.intersectMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result1 = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed

        // Create ExtCore.LongSet sets from the values.
        let longSets = Array.map LongSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result2 = LongSet.intersectMany longSets
        watch.Stop ()
        let result2Time = watch.Elapsed

        // Create ExtCore.HashSet sets from the values.
        let hashSets = Array.map HashSet.ofArray setValues

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result3 = HashSet.intersectMany hashSets
        watch.Stop ()
        let result3Time = watch.Elapsed

        // Create System.Collections.Immutable.ImmutableHashSet sets from the values.
        let immutableHashSets =
            setValues |> Array.map (fun vals -> ImmutableHashSet.Create<int64> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result4 =
            let mutable result = immutableHashSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Intersect immutableHashSets.[i]
            result
        watch.Stop ()
        let result4Time = watch.Elapsed
        watch.Reset ()

        // Create System.Collections.Immutable.ImmutableSortedSet sets from the values.
        let immutableSortedSets =
            setValues |> Array.map (fun vals -> ImmutableSortedSet.Create<int64> vals)

        System.GC.Collect (); System.GC.WaitForPendingFinalizers ()
        watch.Start ()
        let result5 =
            let mutable result = immutableSortedSets.[0]
            for i = 1 to setCount - 1 do
                result <- result.Intersect immutableSortedSets.[i]
            result
        watch.Stop ()
        let result5Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = FSharpCore.Set.toArray result1)
        assert (Set.toArray baseline = LongSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time;
          ``System.Collections.Immutable.ImmutableHashSet`` = result4Time;
          ``System.Collections.Immutable.ImmutableSortedSet`` = result5Time; }

