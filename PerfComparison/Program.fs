// FSharp.Core vs. FSharpCore performance comparisons.

open System.Diagnostics

let randArray count =
    let rand = System.Random ()
    Array.init count <| fun _ ->
        rand.Next ()


[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code
