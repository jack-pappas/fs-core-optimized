// FSharp.Core vs. FSharpCore performance comparisons.

open System.Diagnostics

type TestResult<'T when 'T : comparison> = {
    Baseline : 'T;
    Result : 'T;
}

let randArray count =
    let rand = System.Random ()
    Array.init count <| fun _ ->
        rand.Next ()

//
let createRandomSet count =
    let values = randArray count
    //let watch = System.Diagnostics.Stopwatch.StartNew ()
    let oldSet = Set.ofArray values
    //watch.Stop ()
    //let oldTime = watch.Elapsed
    //watch.Reset ()
    System.GC.Collect ()
    //watch.Start ()
    let newSet = FSharpCore.Set.ofArray values
    //watch.Stop ()
    //let newTime = watch.Elapsed

    //{ Baseline = oldTime; Result = newTime; }
    ()


// Warm-up
printf "Warming up..."
createRandomSet 10000
|> ignore
printfn "done."
printfn ""

let result = createRandomSet 1000000
//printfn "Create Random Set<int> (n=1000000)"
//printfn "Baseline: %4f (ms)" result.Baseline.TotalMilliseconds
//printfn "Result: %4f (ms)" result.Result.TotalMilliseconds




printfn ""
printfn "Press any key to exit..."
System.Console.ReadKey () |> ignore

