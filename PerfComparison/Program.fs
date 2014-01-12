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

namespace PerfComparison

open PerfComparison.Tests


//
[<RequireQualifiedAccess>]
module Benchmark =
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

    /// Benchmark for set creation.
    let create seed density setSize =
        // Test 32-bit integers.
        let resultInt32 = Create.int32 seed setSize System.Int32.MaxValue density
        printfn "Create Random Set<int> (n=%i)" setSize
        TestResult<_>.PrintTimings resultInt32

        // Test 64-bit integers.
        let resultInt64 = Create.int64 seed setSize System.Int64.MaxValue density
        printfn "Create Random Set<int64> (n=%i)" setSize
        TestResult<_>.PrintTimings resultInt64

    /// Benchmark for set union operation.
    let union seed density setSize setCount =
        // Test 32-bit integers.
        let resultInt32 = Union.int32 seed setSize setCount System.Int32.MaxValue density
        printfn "Union Random Set<int> (n=%i, N=%i)" setSize setCount
        TestResult<_>.PrintTimings resultInt32

        // Test 64-bit integers.
        let resultInt64 = Union.int64 seed setSize setCount System.Int64.MaxValue density
        printfn "Union Random Set<int64> (n=%i, N=%i)" setSize setCount
        TestResult<_>.PrintTimings resultInt64

    /// Benchmark for set intersection operation.
    let intersection seed density setSize setCount =
        // Test 32-bit integers.
        let resultInt32 = Intersect.int32 seed setSize setCount System.Int32.MaxValue density
        printfn "Intersect Random Set<int> (n=%i, N=%i)" setSize setCount
        TestResult<_>.PrintTimings resultInt32

        // Test 64-bit integers.
        let resultInt64 = Intersect.int64 seed setSize setCount System.Int64.MaxValue density
        printfn "Intersect Random Set<int64> (n=%i, N=%i)" setSize setCount
        TestResult<_>.PrintTimings resultInt64
    

module Program =
    open LanguagePrimitives
    open ExtCore.Args

    //
    [<EntryPoint>]
    let main args =
        // Print header.
        printfn "Results from running PerfComparison (https://github.com/jack-pappas/fs-core-optimized)"

        (* Variables to hold parsed command-line arguments. *)
        
        /// Density parameter for randomly-generated sets.
        /// Must be in the range (0, 1].
        let argDensity = ref None
        /// The random number generator seed.
        let argRngSeed = ref None

        /// Command-line options.
        let usage =
            [|  ArgInfo.Create ("--density", ArgType.Float (fun f -> argDensity := Some f),
                    "The density parameter for randomly-generated sets. This value must be in the range (0, 1].");
                ArgInfo.Create ("--rng-seed", ArgType.Int (fun i -> argRngSeed := Some i),
                    "A 32-bit integer to use as the seed for the random number generator."); |]

        // Parses argument values which aren't specified by flags.
        let plainArgParser _ =
            // If the input filename has already been set, print a message
            // to the screen, then exit with an error code.
            printfn "Error: Unknown command line flags specified."
            exit 1

        // Parse the command-line arguments.
        ArgParser.Parse (usage, plainArgParser, "PerfComparison <filename>")

        // Validate parsed command line options.
        !argDensity
        |> Option.iter (fun argDensity ->
            if argDensity < GenericZero || argDensity >= GenericOne then
                printfn "Invalid value specified for the --density flag. The value must be in the rand (0, 1]."
                exit 1)

        (* Get random values for parameters which haven't been specified on the command line. *)

        let rng = System.Random ()

        let density =
            !argDensity
            |> Option.fillWith (fun () ->
                // We want a value in the range [0.001, 0.999].
                let mutable d = rng.NextDouble ()
                while d < 0.001 || d > 0.999 do
                    d <- rng.NextDouble ()
                d)

        let rngSeed =
            !argRngSeed
            |> Option.fillWith (fun () ->
                rng.Next ())

        // Print the density parameter and seed value.
        printfn "Random set density parameter: %f" density
        printfn "RNG seed: %i" rngSeed
        printfn "----"
        printfn ""

        (* Warm up so JIT overhead won't affect timings. *)
        Benchmark.warmup rngSeed density

        (* Run the benchmarks *)
        do
            let setSize = 1000000
            Benchmark.create rngSeed density setSize
        
        do
            let setSize = 1000
            let setCount = 10000
            Benchmark.union rngSeed density setSize setCount
            Benchmark.intersection rngSeed density setSize setCount

        (* Wait for a key to exit *)

        printfn ""
        if System.Environment.UserInteractive then
            printfn "Press any key to exit..."
            System.Console.ReadKey () |> ignore

        0   // Exit code

