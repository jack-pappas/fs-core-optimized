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



// Warm-up
printf "Warming up..."
RandomSet.int32 10000 1000000 0.9
|> ignore
printfn "done."
printfn ""

// Test 32-bit integers.
let resultInt32 = RandomSet.int32 1000000 1000000 0.9
printfn "Create Random Set<int> (n=1000000)"
printfn "Baseline: %4f (ms)" resultInt32.Baseline.TotalMilliseconds
printfn "Result: %4f (ms)" resultInt32.Result.TotalMilliseconds
printfn ""

// Test 64-bit integers.
let resultInt64 = RandomSet.int64 1000000 100000000L 0.9
printfn "Create Random Set<int64> (n=1000000)"
printfn "Baseline: %4f (ms)" resultInt64.Baseline.TotalMilliseconds
printfn "Result: %4f (ms)" resultInt64.Result.TotalMilliseconds
printfn ""



printfn ""
printfn "Press any key to exit..."
System.Console.ReadKey () |> ignore

