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

(*** FSharp.Core vs. FSharpCore vs. ExtCore performance comparisons. ***)

module PerfComparison.Program

open PerfComparison.Tests


//
let warmup seed density =
    printf "Warming up..."
    
    Create.int32 seed 100 System.Int32.MaxValue density |> ignore
    Create.int64 seed 100 System.Int64.MaxValue density |> ignore
    
    Union.int32 seed 100 10 System.Int32.MaxValue density |> ignore
    Union.int64 seed 100 10 System.Int64.MaxValue density |> ignore

    Intersect.int32 seed 100 10 System.Int32.MaxValue density |> ignore
    Intersect.int64 seed 100 10 System.Int64.MaxValue density |> ignore

    printfn "done."
    printfn ""

//
let benchmark seed density =
    (* Set creation *)

    // Test 32-bit integers.
    let resultInt32 = Create.int32 seed 1000000 System.Int32.MaxValue density
    printfn "Create Random Set<int> (n=1000000)"
    TestResult<_>.PrintTimings resultInt32

    // Test 64-bit integers.
    let resultInt64 = Create.int64 seed 1000000 System.Int64.MaxValue density
    printfn "Create Random Set<int64> (n=1000000)"
    TestResult<_>.PrintTimings resultInt64


    (* Set union *)

    // Test 32-bit integers.
    let resultInt32 = Union.int32 seed 1000 10000 System.Int32.MaxValue density
    printfn "Union Random Set<int> (n=1000, N=10000)"
    TestResult<_>.PrintTimings resultInt32

    // Test 64-bit integers.
    let resultInt64 = Union.int64 seed 1000 10000 System.Int64.MaxValue density
    printfn "Union Random Set<int64> (n=1000, N=10000)"
    TestResult<_>.PrintTimings resultInt64


    (* Set intersection *)

    // Test 32-bit integers.
    let resultInt32 = Intersect.int32 seed 1000 10000 System.Int32.MaxValue density
    printfn "Intersect Random Set<int> (n=1000, N=10000)"
    TestResult<_>.PrintTimings resultInt32

    // Test 64-bit integers.
    let resultInt64 = Intersect.int64 seed 1000 10000 System.Int64.MaxValue density
    printfn "Intersect Random Set<int64> (n=1000, N=10000)"
    TestResult<_>.PrintTimings resultInt64
    

module Program =
    /// Density parameter for randomly-generated sets.
    /// Must be in the range (0, 1].
    let [<Literal>] defaultDensity = 0.85

    //
    [<EntryPoint>]
    let main args =
        // Print header.
        printfn "Results from running PerfComparison (https://github.com/jack-pappas/fs-core-optimized)"

        // TODO : Get the density from command-line args.
        // TEMP : Just use a fixed density value.
        /// Density parameter for randomly-generated sets.
        /// Must be in the range (0, 1].
        let density = defaultDensity

        // TODO : Get the random seed from command-line args.
        // TEMP : Just generate a random seed.
        let seed =
            let rng = System.Random()
            rng.Next ()

        // Print the density parameter and seed value.
        printfn "Random set density parameter: %f" density
        printfn "RNG seed: %i" seed
        printfn "----"
        printfn ""

        (* Warm up so JIT overhead won't affect timings. *)
        warmup seed density

        (* Run the benchmark *)
        benchmark seed density

        (* Wait for a key to exit *)

        printfn ""
        if System.Environment.UserInteractive then
            printfn "Press any key to exit..."
            System.Console.ReadKey () |> ignore

        0   // Exit code

