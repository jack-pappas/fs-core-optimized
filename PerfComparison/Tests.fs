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
        let oldSet = Set.ofArray values
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let newSet = FSharpCore.Set.ofArray values
        watch.Stop ()
        let newTime = watch.Elapsed

        { Baseline = oldTime; Result = newTime; }

    //
    let int64 count maxValue density =
        let values = RandomArray.int64 count maxValue density
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let _ = Set.ofArray values
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()
        System.GC.Collect ()
        watch.Start ()
        let _ = FSharpCore.Set.ofArray values
        watch.Stop ()
        let newTime = watch.Elapsed

        { Baseline = oldTime; Result = newTime; }


/// Functions for benchmarking the set union operation.
module Union =
    //
    let int32 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let oldResult = Set.unionMany standardSets
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let newResult = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let newTime = watch.Elapsed

        // Verify the results.
        assert (Set.toArray oldResult = FSharpCore.Set.toArray newResult)

        { Baseline = oldTime; Result = newTime; }

    //
    let int64 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let oldResult = Set.unionMany standardSets
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let newResult = FSharpCore.Set.unionMany optSets
        watch.Stop ()
        let newTime = watch.Elapsed

        // Verify the results.
        assert (Set.toArray oldResult = FSharpCore.Set.toArray newResult)

        { Baseline = oldTime; Result = newTime; }


/// Functions for benchmarking the set intersection operation.
module Intersect =
    //
    let int32 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int32 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let oldResult = Set.intersectMany standardSets
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let newResult = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let newTime = watch.Elapsed

        // Verify the results.
        assert (Set.toArray oldResult = FSharpCore.Set.toArray newResult)

        { Baseline = oldTime; Result = newTime; }

    //
    let int64 elementsPerSet setCount maxValue density =
        let setValues =
            Array.init setCount <| fun _ ->
                RandomArray.int64 elementsPerSet maxValue density

        // Create F# Sets from the values.
        let standardSets = Array.map Set.ofArray setValues
        
        System.GC.Collect ()
        let watch = System.Diagnostics.Stopwatch.StartNew ()
        let oldResult = Set.intersectMany standardSets
        watch.Stop ()
        let oldTime = watch.Elapsed
        watch.Reset ()

        // Create fs-core-optimized sets from the values.
        let optSets = Array.map FSharpCore.Set.ofArray setValues

        System.GC.Collect ()
        watch.Start ()
        let newResult = FSharpCore.Set.intersectMany optSets
        watch.Stop ()
        let newTime = watch.Elapsed

        // Verify the results.
        assert (Set.toArray oldResult = FSharpCore.Set.toArray newResult)

        { Baseline = oldTime; Result = newTime; }




