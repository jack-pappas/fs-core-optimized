// FSharp.Core vs. FSharpCore performance comparisons.

open System.Diagnostics

type TestResult<'T when 'T : comparison> = {
    Baseline : 'T;
    Result : 'T;
}

/// Functions for creating arrays of random values.
module RandomArray =
    /// Creates a random array of 32-bit integers.
    let int32 count maxValue density : int[] =
        // Preconditions
        if count < 0 then
            invalidArg "count" "The count cannot be negative."
        elif maxValue < 0 then
            invalidArg "maxValue" "The maximum value cannot be negative."
        elif density < 0.0 then
            invalidArg "density" "The density value cannot be negative."
        elif density > 1.0 then
            invalidArg "density" "The density value cannot be greater than one (1)."

        let rand = System.Random ()
        let maxValue = int <| (float maxValue) * (1.0 - density)
        let arr = Array.zeroCreate count
        for i = 0 to count - 1 do
            arr.[i] <- rand.Next maxValue
        arr

    /// Creates a random array of 64-bit integers.
    let int64 count (maxValue : int64) density : int64[] =
        // Preconditions
        if count < 0 then
            invalidArg "count" "The count cannot be negative."
        elif maxValue < 0L then
            invalidArg "maxValue" "The maximum value cannot be negative."
        elif density < 0.0 then
            invalidArg "density" "The density value cannot be negative."
        elif density > 1.0 then
            invalidArg "density" "The density value cannot be greater than one (1)."

        let rand = System.Random ()
        let maxValue = int64 <| (float maxValue) * (1.0 - density)
        let arr = Array.zeroCreate count
        let bytes = Array.zeroCreate sizeof<int64>
        for i = 0 to count - 1 do
            arr.[i] <-
                rand.NextBytes bytes
                System.BitConverter.ToInt64 (bytes, 0) % maxValue
        arr


/// Testing functions for timing the creation of sets of random values.
module RandomSet =
    (* Without timing (for profiling) *)
    ////
    //let createRandomSet count =
    //    let values = randArray count
    //    let _ = Set.ofArray values
    //    System.GC.Collect ()
    //    let _ = FSharpCore.Set.ofArray values
    //    ()
    //
    //// Warm-up
    //printf "Warming up..."
    //createRandomSet 10000
    //|> ignore
    //printfn "done."
    //printfn ""
    //
    //do createRandomSet 1000000


    (* With timing *)

    //
    let int32Create count maxValue density =
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
    let int64Create count maxValue density =
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

    //
    let int32Union elementsPerSet setCount maxValue density =
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
    let int64Union elementsPerSet setCount maxValue density =
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

    //
    let int32Intersect elementsPerSet setCount maxValue density =
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
    let int64Intersect elementsPerSet setCount maxValue density =
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


(* Warm up *)
do
    printf "Warming up..."
    RandomSet.int32Create 10000 1000000 0.9 |> ignore
    RandomSet.int32Union 10 10 10000000 1.0 |> ignore
    printfn "done."
    printfn ""

(* Set creation *)
do
    // Test 32-bit integers.
    let resultInt32Create = RandomSet.int32Create 1000000 System.Int32.MaxValue 0.85
    printfn "Create Random Set<int> (n=1000000)"
    printfn "Baseline: %4f (ms)" resultInt32Create.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt32Create.Result.TotalMilliseconds
    printfn ""

    // Test 64-bit integers.
    let resultInt64Create = RandomSet.int64Create 1000000 System.Int64.MaxValue 0.85
    printfn "Create Random Set<int64> (n=1000000)"
    printfn "Baseline: %4f (ms)" resultInt64Create.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt64Create.Result.TotalMilliseconds
    printfn ""


(* Set union *)
do
    // Test 32-bit integers.
    let resultInt32Union = RandomSet.int32Union 1000 10000 System.Int32.MaxValue 0.85
    printfn "Union Random Set<int> (n=1000, N=10000)"
    printfn "Baseline: %4f (ms)" resultInt32Union.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt32Union.Result.TotalMilliseconds
    printfn ""

    // Test 64-bit integers.
    let resultInt64Union = RandomSet.int64Union 1000 10000 System.Int64.MaxValue 0.85
    printfn "Union Random Set<int64> (n=1000, N=10000)"
    printfn "Baseline: %4f (ms)" resultInt64Union.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt64Union.Result.TotalMilliseconds
    printfn ""

(* Set intersection *)
do
    // Test 32-bit integers.
    let resultInt32Intersect = RandomSet.int32Intersect 1000 10000 System.Int32.MaxValue 0.85
    printfn "Intersect Random Set<int> (n=1000, N=10000)"
    printfn "Baseline: %4f (ms)" resultInt32Intersect.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt32Intersect.Result.TotalMilliseconds
    printfn ""

    // Test 64-bit integers.
    let resultInt64Intersect = RandomSet.int64Intersect 1000 10000 System.Int64.MaxValue 0.85
    printfn "Intersect Random Set<int64> (n=1000, N=10000)"
    printfn "Baseline: %4f (ms)" resultInt64Intersect.Baseline.TotalMilliseconds
    printfn "Result: %4f (ms)" resultInt64Intersect.Result.TotalMilliseconds
    printfn ""
    




printfn ""
printfn "Press any key to exit..."
System.Console.ReadKey () |> ignore

