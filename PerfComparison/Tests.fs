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

open System.Diagnostics
open PerfComparison


/// Functions for benchmarking set creation (and by correlation, the add/insert function).
module Create =
    //
    let int32 count maxValue density =
        let values = RandomArray.int32 count maxValue density
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.ofArray values
        watch.Stop ()
        let baselineTime = watch.Elapsed

        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.ofArray values
        watch.Stop ()
        let result1Time = watch.Elapsed
        
        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result2 = IntSet.ofArray values
        watch.Stop ()
        let result2Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result3 = HashSet.ofArray values
        watch.Stop ()
        let result3Time = watch.Elapsed

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time; }

    //
    let int64 count maxValue density : TestResult4<_> =
        let values = RandomArray.int64 count maxValue density
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.ofArray values
        watch.Stop ()
        let baselineTime = watch.Elapsed
        
        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.ofArray values
        watch.Stop ()
        let result1Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result2 = LongSet.ofArray values
        watch.Stop ()
        let result2Time = watch.Elapsed

        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let result3 = HashSet.ofArray values
        watch.Stop ()
        let result3Time = watch.Elapsed

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time;
          ``ExtCore (HashSet)`` = result3Time; }


/// Functions for benchmarking the set union operation.
module Union =
    //
    let int32 elementsPerSet setCount maxValue density : TestResult3<_> =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.unionMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.IntSet sets from the values.
        let intSets = Array.map IntSet.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result2 = IntSet.unionMany intSets
        watch.Stop ()
        let result2Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = IntSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time; }

    //
    let int64 elementsPerSet setCount maxValue density : TestResult3<_> =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.unionMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed

        // Create ExtCore.LongSet sets from the values.
        let longSets = Array.map LongSet.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result2 = LongSet.unionMany longSets
        watch.Stop ()
        let result2Time = watch.Elapsed
        watch.Reset ()

        // Verify the results.
        assert (Set.toArray baseline = FSharpCore.Set.toArray result1)
        assert (Set.toArray baseline = LongSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time; }


/// Functions for benchmarking the set intersection operation.
module Intersect =
    //
    let int32 elementsPerSet setCount maxValue density : TestResult3<_> =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.intersectMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed
        watch.Reset ()

        // Create ExtCore.IntSet sets from the values.
        let intSets = Array.map IntSet.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result2 = IntSet.intersectMany intSets
        watch.Stop ()
        let result2Time = watch.Elapsed

        // Verify the results.
        assert (Set.toArray baseline = IntSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time; }

    //
    let int64 elementsPerSet setCount maxValue density : TestResult3<_> =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let baseline = Set.intersectMany standardSets
        watch.Stop ()
        let baselineTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result1 = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let result1Time = watch.Elapsed

        // Create ExtCore.LongSet sets from the values.
        let longSets = Array.map LongSet.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let result2 = LongSet.intersectMany longSets
        watch.Stop ()
        let result2Time = watch.Elapsed

        // Verify the results.
        assert (Set.toArray baseline = FSharpCore.Set.toArray result1)
        assert (Set.toArray baseline = LongSet.toArray result2)

        { ``FSharp.Core (Original)`` = baselineTime;
          ``FSharp.Core (Optimized)`` = result1Time;
          ``ExtCore (Patricia Trie)`` = result2Time; }

