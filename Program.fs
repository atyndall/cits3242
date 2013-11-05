#light

// Programming Paradigms Project

//module DistributedExperimentUnification

open System
open System.Threading
open System.Collections.Generic
open System.Windows.Forms          // Note that you'll need references for System.Windows.Forms and
open System.Drawing                // System.Drawing  (See the "solution explorer", on the right in VS...)  ----->>> 
open Microsoft.FSharp.Control

/// Generate a random positive integer in 1..n
let random = let myRand = Random() in myRand.Next
             
/// Sleep for n milliseconds
let sleep (n:int) = Thread.Sleep n

/// Sleep for between 1 and some number of milliseconds
let sleepUpTo (n:int) = sleep (1 + random n)

/// Make a named thread that runs f
let mkThread name f = Thread (ThreadStart f, Name=name)
/// Make a named thread and start it immediately
let startThread name f = (mkThread name f).Start()

/// wait until another thread signals the given object has changed
let waitFor obj = ignore(Monitor.Wait obj)
/// wake up all threads waiting on a given object
let wakeWaiters obj = Monitor.PulseAll obj


////////////////////////////////////// Debugging Output 

Application.EnableVisualStyles()
let newLine = Environment.NewLine

/// A window with colour text output indicating on the object a thread is in.
type outputForm() =
       let pr = ref (fun cl str -> ())  // stub - the actual function is put in later
       let ready = ref false
       member this.Pr str = (!pr) str
       member this.WaitUntilReady() = lock this <| fun()-> while not !ready do waitFor this
       member this.Run() =                              // You can adjust the window size, etc, below as appropriate.
           let form = new Form(Text="Event interleaving",Size=Drawing.Size(1600, 1000),Visible=true)  
           let textB = new RichTextBox(Dock= DockStyle.Fill, Multiline=true, ReadOnly=true, 
                                       Font=new Font(familyName="Courier New", emSize=8.0f), BackColor=Color.Black)
           do textB.SelectionStart<-textB.TextLength ; textB.ScrollToCaret()
           let color n = let colors = [| Color.DodgerBlue; Color.Coral; Color.OliveDrab; Color.Violet;  Color.Gold; 
                                         Color.DimGray; Color.IndianRed;  Color.GreenYellow;  Color.BlueViolet; Color.White |]
                         if n>=0 then colors.[n%colors.Length] else Color.White
           pr := fun cl str -> let doPr() = textB.SelectionStart <- textB.TextLength; textB.SelectionColor<-color cl; 
                                            textB.SelectedText <- str+newLine; form.Show()                                          
                               if textB.InvokeRequired then 
                                  form.Invoke (Action doPr) |> ignore
                               else doPr()
           do form.Controls.Add(textB)
           do form.Show()
           do ready:=true; lock this <| fun()-> wakeWaiters this
           textB.Focus() |> ignore
           Application.Run(form)

let form = outputForm()                        
startThread "WinForms" form.Run
form.WaitUntilReady()

/// The time the system started.
let startTime = ref DateTime.Now // This is reset when a test sequence is started.

// Various functions for printing events to both the console and the coloured events window.
// They generally can be easily added at the end of a line to print a result via |> prIdent n prefixString
// Use a clientID of -1 for a print not related to a client.
let prLock = ref ()
let prRaw clientID str = lock prLock <|fun()->form.Pr clientID str; printfn "%s" str
let prFmt format args = prRaw 0 (sprintf format args)                                
let prStamp clientID pre str = let prefix = sprintf "%6.0f %s" (DateTime.Now - !startTime).TotalMilliseconds pre
                               let indent =  String.map (fun _-> ' ')  prefix
                               prRaw clientID ((sprintf "%s %s" prefix str).Replace("\n","\n"+indent))
let pr clientID pre res = prStamp clientID pre (sprintf "%A" res) ; res
let pr0 pre res = pr 0 pre res
let prIndStr clientID pre str = let indent =  String ( Array.map (fun _-> ' ') [|1..8+8*clientID|] )
                                prStamp clientID (indent+pre) str
let prIndent clientID pre res = prIndStr clientID pre (sprintf "%A" res); res

// These can be handy for debugging: swap them to the commented versions to turn on debug prints.
// (The VS threads window may also be useful for debugging.)
let dbg clientID pre res = res // pr clientID pre res
let dbgIndent clientID pre res = res // prIdent clientID pre res 





//////////////////////////////////////// Types for experiments, rules, etc.

type exp = A | B | Mix of exp * exp | Var of string

/// The value (e, ee) represents that "e suffices instead of ee" or "e suff ee" for short - see the rule type.
type sufficency = exp * exp  

/// The value (e, ee), [(e1,ee1) ... (eN,eeN)] represents the rule that: "E suff EE provided that for all i in 1..N, Ei suff EEi".  
/// Here the E, EE, Ei, EEi are the same as e, ee, eI, eeI except with each variable (Var Vj) replaced by an experiment EEEj that 
/// contains no eVarSet (the same EEEj each time Vj appears in the rule).  The rule holds for every such substitution for the eVarSet. 
type rule = Rule of sufficency * (sufficency list)  

type ruleGen = unit -> rule      // A rule generator creates new variables for a rule each time it is called, to avoid clashes
                                 // with variable names in other rules, or when the rule is used multiple times.
type labRules = ruleGen list     // Each lab has a list of rules, represented as generators.


// Types for identifying labs and clients
type labID = int
type clientID = int

/// The number of Bases and Mixes in an experiment
let rec expSize = function A|B -> 1
                         | Mix (x, y) -> 1+expSize x + expSize y
                         | Var _ -> raise (Exception "expSize for a Var")       // This shouldn't happen



/////////////////////////////////////////////////                        
/////  Put your code for the first part here                         
/////////////////////////////////////////////////

// Hints:  First, see the hints on the project handout. Then the following are hints to help get you started. 
//  1. Decompose the problem of finding possible combined experiments into simpler steps.
//  2. The basic step will be checking "e suffices instead of E" for two experiments, using the set of 
//     rules for a particular lab.  Use a function "suffices" taking the rules and two experiments.
//  3. To use a rule to show a particular sufficiency like "E suffices instead of EE", all you need to do is choose 
//     an appropriate experiment EEEj for each variable Vj in the rule in order to turn e into E and ee into EE, and then 
//     attempt to show sufficiency for each pair (E1, EE1) ... (En, EEn) - these are called the subgoals.  Note that if n=0 there is
//     nothing more to do, and every lab has at least one rule like this.  (The rules will always be designed so that
//     it is impossible to keep following subgoals forever, although not if you have bugs, so you may want to limit this.) 
//
//     Note that variables can appear many times, including many times in the same experiment.
//     E.g., the following represents a rule that roughly means 
//     "doing an experiment x always suffices instead of doing x twice and mixing the results"
//          (Var "x", Mix (Var "x", Var "x")), []
// 4. Each time a rule is used, a single experiment is chosen to replace each variable.  But,
//    if the rule is used again, different experiments can be chosen.
//
// 5. To match experiments to rules, you will probably need a function "unify" that takes two exp's and returns a 
//    substitution that makes the exp's exactly the same when it is used to replace the eVarSet in one of the exp's 
//    (if such a substitution exists).   For example:
//
//           unify (Mix (A, B)) (Mix (Var "x", A)) yields no substitution the two exp's can't be made the same.
//
//           unify (Mix (A, B)) (Mix (Var "x", Var "y")) yields a substitution that maps: "x" to A  and "y" to B
//
//           unify (Mix (A, A)) (Mix (Var "x", Var "x")) yields a substitution that maps: "x" to A 
//
//            unify (Mix (A, B)) (Mix (Var "x", Var "x")) yields no substitution, because no matter
//               what we replace Var "x" with, the two exp's won't end up the same 
//               ("x" can't be equal to both A and B).
//
//  6. Write unify by considering the possible cases for the two exps, and using recursion appropriately.
//  7. You will need a type for substitutions - mappings from variable names to exp's they should be replaced with.
//  8. Be careful not the create substitutions that map a variable to an exp that contains the same variable. (!)
//  9. You can modify the exact form of the unify function if you want.
// 10. Use this function write one that tries unifying one exp with each part of another exp.
// 11. Eventually you need a function that takes a number clients exps, generates all possible combined exps,
//     then chooses between them using an efficiency function like the one above.
// 12. A smaller experiment with the same number of clients should be preferred over a larger one.

/// Maximum recursion depth when attempting recursive behaviour.
let maxRuleDepth = 8

/// Format of substitutions
type subs = Map<string, exp>



///// OPTION HELPERS

/// Applies f to o1 and o2 if they are both Some, else returns None.
/// f is a function that returns its own Option.
let oIf f (o1 : 'a option) (o2 : 'b option) =
    match o1.IsNone, o2.IsNone with
    | false, false -> f o1.Value o2.Value
    | _            -> None

/// Applies f to o1 and o2 if they are both Some, else returns None.
/// f is a function that returns any value and is wrapped.
let oIf2 f (o1 : 'a option) (o2 : 'b option) =
    match o1.IsNone, o2.IsNone with
    | false, false -> Some(f o1.Value o2.Value)
    | _            -> None

/// Merges two options into one, with any None propagating to the top.
let oMerge (o1 : 'a option) (o2 : 'b option) =
    oIf (fun x y -> Some(x, y)) o1 o2

/// Infix operator that applies a function y if x is Some, or false otherwise
let (>.>) (x:'a option) (y:'a->bool) =
    x.IsSome && x.Value |> y



///// MAP HELPERS

/// Accepts two maps that must be merged together.
/// If either of the maps are None, the function returns None.
/// Otherwise, we attempt to merge the keys of the map.
/// If either or both of the maps are empty, the non-empty map is returned, or an empty map is returned.
/// If the same key in the two maps is assigned a different value, the function removes them from the merge.
/// If we end up with a map that is completely empty after this duplicate removal process, the merge has failed, and we return None.
let mMerge u1 u2 =
    let mMerge (a : subs) (b : subs) =
        match a.IsEmpty, b.IsEmpty with
        | true,  true  -> Some(Map.empty)
        | true,  false -> Some(b)
        | false, true  -> Some(a)
        | false, false -> let merged = Map.fold (fun s k v ->
                                   match Map.tryFind k s with
                                   | Some v' when v <> v'                  -> Map.remove k s
                                   | _                                     -> Map.add k v s)  a b
        
                          match Map.isEmpty merged with 
                          | true -> None
                          | _    ->    Some(merged)

    oIf mMerge u1 u2



///// EXPERIMENT HELPERS

/// Attempts to substitute map into exp.
/// Returns Some(substituted result) or None if not all variables in the provided exp can be substituted.
let rec eMap map exp =
    let eMap = eMap map

    match exp with
    | Var(k)    -> Map.tryFind k map
    | Mix(a, b) -> oIf2 (fun x y -> Mix(x,y)) (eMap a) (eMap b)
    | a         -> Some(a)


/// Returns true if var exists within exp, false otherwise.
let rec eVar = function
    | Var(x)    -> true
    | Mix(x, y) -> eVar x || eVar y
    | _         -> false

/// Returns set of all Vars found in given experiment.
let rec eVarSet = function
    | A | B       -> Set.empty
    | Var(_) as x -> Set.empty.Add x
    | Mix(a, b)   -> Set.union (eVarSet a) (eVarSet b)
    


///// LIST HELPERS

/// Generic function that accepts an f2 and f2 that are applied in a chain to suffs.
let lmGen f1 f2 suffs = 
    suffs |>
    Seq.ofList |>
    Seq.groupBy f1 |>
    Seq.map (fun (k, v) -> (k, [for e in v -> f2 e])) |>
    Map.ofSeq

/// Collapses [(x,y); (x,z)] into Map(y -> [x]; z -> [x])
let lmOut suffs = lmGen snd fst suffs

/// Collapses [(x,y); (x,z)] into Map(x -> [y; z])
let lmIn suffs = lmGen fst snd suffs

/// Replaces all instances of a with b in suffs.
/// If any (a, a) are created where a = a, that tuple is excluded.
let lReplace suffs a b =
    suffs |>
    List.map (fun (k, v) -> 
        let nk = if k = a then b else k
        let nv = if v = a then b else v
        (nk, nv)
    ) |>
    List.filter (fun (k, v) ->
        not (k = b && v = b)
    )

/// Returns cross-product of two lists
let (>@<) l1 l2 =
  [ for el1 in l1 do
        for el2 in l2 do
            yield el1, el2 ]



///// CORE CODE

/// Provided with a list of subsufficiencies and a set of variables that are unknown and must be removed.
/// Returns Some(subsufficiences) reduced to a logically equivalent version that contains no unknown variables.
/// If the implications between the unknown variables cannot be determined, returns None.
let rec reduceTransitive suffs (unknowns:'a Set) =
    /// Returns true if both x and y are in the unknown set
    let bothUnknowns (x, y) =
        unknowns.Contains x && unknowns.Contains y

    /// Remove any tuples from the list if they contain the provided variable
    let removeContains a =
        suffs |> List.filter (fun (k,v) ->
            not (k = a || v = a)
        )

    match unknowns.Count with
    // If there are no more unknowns, remove dupes and terminate
    | 0  -> Some(suffs |> Seq.distinct |> List.ofSeq)

    // If there are still unknowns, continue evaluating
    | _  -> 

        match suffs |> List.tryFind bothUnknowns with
        // In the case of a tuple being both unknowns, we can conclude that they are equal.
        // Replace all instances of one with the other, remove the replaced one from the unknown set, and recurse.
        | Some(k, v) -> reduceTransitive (lReplace suffs v k) (unknowns.Remove v)

        // If there are no more "both unknown" tuples, find instances in which there is an unknown
        // on one side of a tuple, and the same unknown on the opposite side of a different tuple
        // then merge these tuples together.
        // i.e. (a, z) (z, b) -> (a, b) where z is unknown
        | None       -> 
            
            let inmap = lmIn suffs
            let outmap = lmOut suffs
            let u = unknowns.MinimumElement

            let containsU = Map.containsKey u

            // To perform this merging, we calculate the cross-product of the list of inbound and outbound
            // connections for the unknown we are removing, and create them as new connections in the list.
            // We then remove all instances of the now redundant unknown variable, remove it from the set of
            // unknowns, and recurse.
            match containsU inmap, containsU outmap with
            | true, true -> reduceTransitive ( removeContains u @ (outmap.Item u >@< inmap.Item u) ) (unknowns.Remove u)
            | _          -> None

/// Attempts to unify two experiements by providing variable mappings.
/// If mapping is possible, a Some(Map) will be provided with the mappings necessary.
/// If mapping is not possible, or the depth limit is reached, a None will be provided.
let unify exp1 exp2 = 
    let rec unify depth eMap exp1 exp2 =
        let unify = unify (depth + 1) eMap
        
        // Swap variables so that they are on the right-hand side
        let l, r = match (eVar exp1), (eVar exp2) with
                   | true, true  -> raise (Exception("Case should never occur; transitivity is removed before this point"))
                   | true, false -> exp2, exp1 // Simply swap if all eVarSet are on the LHS
                   | _           -> exp1, exp2 // Normal case, either no eVarSet or all eVarSet on RHS
                                      
        if depth = maxRuleDepth then None
        else
            match l, r with
            // Things that are equal don't need to be considered
            | a,b when a = b           -> Some(eMap)

            // Can't match primatives with primatives or mix with primatives; nothing to match.
            | _, A | _, B
            | A, Mix(_) | B, Mix(_)    -> None

            // If we encounter a mix and a mix, we decompose two subproblems, each of these problems
            // respecting the parameter position of the first problem.
            | Mix(f1, f2), Mix(m1, m2) -> mMerge (unify m1 f1) (unify m2 f2)

            // If we encounter anything else and a mix, we decompose two subproblems, each of these
            // problems each eith an identical first value, and then use the different second values.
            | _ as v, Mix(m1, m2)      -> mMerge (unify m1 v) (unify m2 v)

            // We can deduce that whatever tuple is here can be considered a pair; match them together.    
            | _ as v, Var(k)           -> Some(Map.add k v eMap)

    // Begin recursion with base parameters
    unify 0 Map.empty exp1 exp2

/// Checks whether exp1 suffices instead of exp2 according to rules.
/// Will also return false if the maxRuleDepth is reached, or there is a hanging unknown variable.
let suffices rules (exp1, exp2) = 
    let rec suffices depth (rules:(unit->rule) list) (exp1, exp2) = 
        let suffices = suffices (depth + 1)

        /// Unify two swapped exp tuples and merge the resulting maps
        let unifySwap (e1, e2) (f1, f2) = mMerge (unify e1 f1) (unify e2 f2)

        /// Given a rule (sufficiency and a list of subsufficiencies) and a tuple of experiments,
        /// determine whether the rule is valid and satisfied.
        /// Firstly, the experiments' patterns are matched against the variables in the rule.
        /// This attempt to create a valid mapping of variables to experiments.
        /// If this mapping is successful, checkRules then uses a list comprehension on the list
        /// of subsufficiencies, checking whether suffices evaluates to true.
        /// If all subsufficiencies evaluate to true, checkRule evaluates to true.
        let checkRule (R:rule) (e1, e2) =
            let f, subs = match R with Rule(f, s) -> f, s

            let substitution = unifySwap f (e1, e2)

            substitution.IsSome && 
                Seq.fold (&&) true [for (g1, g2) in subs -> 
                                        let m = eMap (substitution.Value)
                                        oMerge (m g1) (m g2) >.> (suffices rules)]

        if depth = maxRuleDepth then false
        else
            /// List scontaining an evaluated version of the rules with transitivity removed
            let evaluated = [for r in rules -> 
                                match r() with
                                | Rule( (qx, qy) as q, s ) -> 
                                    let ruleSeen = Set.union (eVarSet qx) (eVarSet qy)
                                    let suffList = [for (x, y) in s -> Set.union (eVarSet x) (eVarSet y)]
                                    let suffSeen = Seq.fold Set.union Set.empty suffList
                                    let unknowns = suffSeen - ruleSeen

                                    let reduction = reduceTransitive s unknowns
                                    match reduction.IsSome with
                                    | true  -> Some( Rule(q, reduction.Value) )
                                    | false -> None
                            ]

            if List.exists (fun (x:rule option) -> x.IsNone) evaluated then false
            else
                (not rules.IsEmpty) &&
                    Seq.fold (||) false [for r in evaluated -> 
                                            checkRule r.Value (exp1, exp2)]

    // Begin suffices with base parameters
    suffices 0 rules (exp1, exp2)



///// TEST CODE

// These are some handy functions for creating rule generators with different numbers of variables
let newVar =   let n = ref 0 in   fun v -> n:=!n+1;
                                           Var (v + string !n)

let newVar2 v1 v2 = newVar v1, newVar v2
let newVar3 (v1,v2,v3) = newVar v1, newVar v2, newVar v3
let newVar4 (v1,v2,v3,v4) = newVar v1, newVar v2, newVar v3, newVar v4


// These are some rules you can use for testing.
// Consider creating your own and include any interesting ones in your submission.

let rule1 () = let x = newVar "x"
               Rule ((x, x), [])

let rule2 () = let x, xx, y = newVar3 ("x", "xx", "y")
               Rule ((Mix(x,xx), y),  [(x,y)])

let rule3 () = let x, xx, y = newVar3 ("x", "xx", "y")
               Rule ((Mix(x,xx), y),  [(xx,y)])

let rule4 () = Rule ((Mix(A, B), Mix(B, A)), [])
let rule5 () = Rule ((Mix(B, A), Mix(A, B)), [])
let rule6 () = let x, xx, y, yy = newVar4 ("x", "xx", "y", "yy")
               Rule ((Mix(x,xx), Mix(y,yy)),  [(x,y); (xx,yy)])

let rule7 () = let x, xx, y, yy = newVar4 ("x", "xx", "y", "yy")
               Rule ((Mix(x,xx), Mix(y,yy)),  [(x,yy); (xx,y)])

let rule8 () = let x = newVar "x"
               Rule ((x, Mix(x,x)),  [])

let rule9 () = let x, xx, y, z = newVar4 ("x", "xx", "y", "z")
               Rule ( (Mix (x,xx),y),  [(x,z); (z,y)] )

let rule10() = let x, xx, y, z = newVar4 ("x", "xx", "y", "z")
               Rule ( (Mix (x,xx),y),  [(xx,z); (z,y)] )

let rule11() = Rule ( (A,B),  [] )
let rule12() = Rule ( (B,A),  [] )

// Rules to cope with new transitivity definition and behaviour
let rule13() = let z = newVar ("z")
               Rule ( (A,B),  [(z,z);] )

let rule14() = let x, xx, y, z = newVar4 ("x", "xx", "y", "z")
               Rule ( (Mix (x,xx),y),  [(x,y); (z,y)] )

// These are some example sets of rules.  Again, submit any interesting sets you use during testing.  

let rulesA = [rule1; rule2; rule3; rule6]
let rulesB = [rule1; rule2; rule3; rule4; rule5; rule6; rule7; rule8]
let rulesC = [rule4; rule5; rule9; rule10; rule11; rule12]      

// Rules 9,10 are slightly tricky. 
// Focus on rules like the others first.
let correctStr = function false -> "INCORRECT!  "
                        | true -> ""
let prTest pre expected res = pr0 (correctStr (res=expected) + pre + " = ") res |> ignore

suffices [rule1] (A, A) |> prTest "suffices [rule1] (A, A)" true
suffices [rule1] (A, B) |> prTest "suffices [rule1] (A, B)" false
prRaw 0 "\n"

suffices rulesA (A, B) |> prTest "suffices rulesA (A, B)" false
suffices rulesA (Mix (A, B), A) |> prTest "suffices rulesA (Mix (A, B),A)" true 
suffices rulesA (Mix (Mix (A, B), B),A) |> prTest "suffices rulesA (Mix (Mix (A, B), B),A)" true
suffices rulesA (Mix (Mix (B, B), B),A) |> prTest "suffices rulesA (Mix (Mix (B, B), B),A)" false
suffices rulesA (Mix (Mix (B, B), B), Mix (B, B)) |> prTest "suffices rulesA (Mix (Mix (B, B), B), Mix (B, B))" true
suffices rulesA (Mix (Mix (A, B), B), Mix (B, A)) |> prTest "suffices rulesA (Mix (Mix (A, B), B), Mix (B, A))" false
prRaw 0 "\n"

suffices rulesB (A, B) |> prTest "suffices rulesB (A, B)" false
suffices rulesB (Mix (A, B), A) |> prTest "suffices rulesB (Mix (A, B),A)" true
suffices rulesB (Mix (Mix (A, B), B),A) |> prTest "suffices rulesB (Mix (Mix (A, B), B),A)" true
suffices rulesB (Mix (Mix (B, B), B),A) |> prTest "suffices rulesB (Mix (Mix (B, B), B),A)" false
suffices rulesB (Mix (Mix (B, B), B), Mix (B, B)) |> prTest "suffices rulesB (Mix (Mix (B, B), B), Mix (B, B))" true
suffices rulesB (Mix (Mix (A, B), B), Mix (B, A)) |> prTest "suffices rulesB (Mix (Mix (A, B), B), Mix (B, A))" true
prRaw 0 "\n"

suffices rulesC (A, B) |> prTest "suffices rulesC (A, B)" true
suffices rulesC (Mix (A, B), A) |> prTest "suffices rulesC (Mix (A, B),A)" true //Transitive "problem" case.
suffices rulesC (Mix (Mix (A, B), B),A) |> prTest "suffices rulesC (Mix (Mix (A, B), B),A)" true
suffices rulesC (Mix (Mix (B, B), B),A) |> prTest "suffices rulesC (Mix (Mix (B, B), B),A)" true
suffices rulesC (Mix (Mix (B, B), B), Mix (B, B)) |> prTest "suffices rulesC (Mix (Mix (B, B), B), Mix (B, B))" false
suffices rulesC (Mix (Mix (A, B), B), Mix (B, A)) |> prTest "suffices rulesC (Mix (Mix (A, B), B), Mix (B, A))" true // Modified from false to take into account different transivity rules
prRaw 0 "\n"

// New transitivity test rules
suffices [rule13] (A, B) |> prTest "suffices [rule13] (A, B)" true // Should be true as (z, z) is eliminated as meaningless
suffices [rule14] (Mix (A, B), A) |> prTest "suffices [rule14] (Mix (A, B), A)" false // Should be false as rule14 has a hanging variable

//////////  End of Part 1 of the Project


//////////  Project part 2 follows

///////////////////////////////////////////////////////////////////////////
/// The following is the simulation of the labs you should use test your code.
//     NOTE: threads must never contact labs except via DoExp, and only when when the lab is unused.
//     This includes creating locks on the lab objects.
//     You do NOT need to change this class. (You can change it, but I'm likely to change it back during marking.)
//////////////////////////////////////////////////////////////////////////
type lab (labID, rules) =
    let busy = ref false
    let usingClID = ref None  // Stores the client currently using the lab, if there is one.

    member this.Rules = rules
    
    /// Send an experiment to a lab.  The continuation is called with the result of the experiment
    //  when it is complete.
    member this.DoExp delay (exp:exp) clID (continuation : bool->unit) =  
       startThread ("Lab"+ string labID) <| fun ()->
          if !busy then  let str = sprintf "BANG! lab%d explodes - host%d is already using it" labID (!usingClID).Value
                         prStamp -1 str "" //; failwith str // uncomment this to have the whole program fail.
          usingClID := Some clID              
          busy:=true
          sleep delay  // Doing experiment (the delay is provided by the client for ease of testing the prototype)
          busy:=false
          usingClID := None
          if random 2 = 1 then continuation true  else continuation false


//////////////////////////////////////////////////////////////////////////////////////////////////
// You may find the following useful to make actions run after a lock is released - this is otherwise 
// slightly tricky when those actions depend on variables with scopes within the holding of the lock.  E.g.
//     hlock obj <| fun later -> let v = something()
//                               later <| fun()-> someActionUsing v   // Makes the action happen after lock release.

/// Lock an object while running f, but also pass a "hook" to f for making functions run when the lock is released.  
let hLock obj f = let onUnlock = ref (fun() -> ())
                  let later action =  onUnlock := (let u = !onUnlock in fun () -> u(); action())
                  let res = lock obj <| fun()-> f later                 // Execute f, providing the later function
                  (!onUnlock)()
                  res                                   

                                                
///////////////////////////////////////////////////////////////////////////////////
// Add your code for the second part here and below, including in the client class below.
////////////////////////////////////////////////////////////////////////////////////

// Hints:
// 1. You must be very careful here that your implementation is a suitable prototype for a decentralized system,
//    even though you are only building the prototype, not the final system.
// 2. One client's thread may call members on another client via the clients array - this is considered to 
//    indicate that in the final (non-prototype) system a request will sent via the network (and similarly for
//    the value returned by the member).   (This is usually called a Remote Method Invocation.)
// 3. Clients should NEVER pass (nor return) to each other data that is mutable or contains elements that are mutable.
//    Mutable data cannot be sent over the network in the final version.
// 4. Clients should never be contacted when they do not require a lab, and have no lab, except by other labs that
//    have been inactive and have yet to discover that the first client no longer holds a lab.
// 5. You will need a number of other members in the client class for clients to communicate with each other
//    in various situations.
// 6. You will need locking in some of the code in the this class, but be careful of deadlocks.
// 7. You will need some additional mutable state variables in the client class.
// 8. No static mutable variables are allowed, since these can't be decentralized. 
// 9. You will probably want to define a type for queues, but be careful not to pass mutable values between clients.
    


///// TYPE DEFINITIONS
type expResult = bool
type expDelay = int

type wantDo = Queued | AlreadyQueued | WillGift | NoLab
type nowOwn = AcceptOwnership | DeclineOwnership

type rplyWantDo = AsyncReplyChannel<wantDo>
type rplyNowOwn = AsyncReplyChannel<nowOwn>

type rplyWhichClient = AsyncReplyChannel<clientID>
type rplyExpResult = AsyncReplyChannel<expResult>

type expDelayRes = exp * expDelay * rplyExpResult

type queuedClient = clientID * expDelayRes

type clientMsg  = OwnLab       of labID * rplyWhichClient                 //do you own this lab? Return the # of whoever owns it. 
                | WantToDo     of expDelayRes * clientID * rplyWantDo //I want to do experiment 
                | NowOwn       of labID * queuedClient list * rplyNowOwn //You now own labID (if you want it)
                | NewExp       of expDelayRes
                | ExpComplete  of clientID * expResult * exp
                | GiftComplete of labID * clientID * nowOwn
                | ARplyWantDo  of labID * clientID * wantDo 
                | ARplyExpDone of expResult * queuedClient list
                | Terminate

type state = Idle | Waiting | Busy | Gifting | Termination
      


///// HELPER FUNCTIONS
let DEBUG = false

/// Starts the async r with the continuation v
let asyncStart r v = Async.StartWithContinuations(r,v,(fun _ -> ()),(fun _ -> ()))

/// 3-Tuple functions
let fst3 (a,b,c) = a
let snd3 (a,b,c) = b
let thd3 (a,b,c) = c

/// Helper function to see if Seq contains item
let contains x = Seq.exists ((=) x)

/// F# version of the .NET Queue Peek
let tryPeek (q:Queue<'a>) =
    try
        Some(q.Peek())
    with
    | :? InvalidOperationException -> None

/// F# version of the .NET Queue Dequeue
let tryDequeue (q:Queue<'a>) =
    try
        Some(q.Dequeue())
    with
    | :? InvalidOperationException -> None



///// CORE CODE

/// Uses the suffices function to get the best experiment to use
let bestExp (ours:expDelayRes) (theirs:queuedClient list) (lid:labID) (labs:lab[] ref) clientID =
    let rules:labRules = (!labs).[lid].Rules
    let compatible = [for (c,(e,f,g)) as a in ((clientID,ours) :: theirs) -> if not (suffices rules (fst3 ours,e)) then
                                                                               ([], expSize e, a)
                                                                             else 
                                                                               ([for (_,(e2,_,_)) as b in theirs do if (suffices rules (e,e2)) then printfn "%A suffices for %A" e e2
                                                                                                                                                    yield b], expSize e, a)]
     
    printfn "%A" compatible

    ((compatible |> List.sortBy (fun (x,y,z) -> (x.Length,y)) |> List.map (fun (x,y,z) -> (x,z)) |> List.rev).Head)



/// A class for clients that coordinate and unify experiments before sending them to labs.  
/// (You need to finish this class.)
type client (clientID, numLabs) =
    /// Array of known clients
    let clients:client[] ref = ref Array.empty

    /// Array of known labs
    let labs:lab[] ref = ref Array.empty

    /// The client coordinating each lab, according to the most recent information known by this client.
    let lastKnownCoord = Array.init numLabs (fun labID -> labID)  // Initially client i has lab i, for i=0..numLabs-1

    /// Experiments that need to be run
    let expsToRun = new Queue<expDelayRes>()

    /// If you don't own a lab, you will have a array of labs you want to use
    let queuedLabs = new List<labID>()

    /// If you own a lab, you will have a queue of clients queued for your lab
    let queuedClients = new Queue<clientID>()

    /// Exps for clients
    let queuedClientExps:expDelayRes option[] ref = ref Array.empty

    // Debugging functions
    let prStr (pre:string) str = if DEBUG then prIndStr clientID (sprintf "Client%d: %s" clientID pre) str 
                                 else printfn ("Client%d: %s %s") clientID pre str
    let prStr2 (pre:string) str = prIndStr clientID (sprintf "Client%d: %s" clientID pre) str 
    let pr (pre:string) res = prStr pre (sprintf "%A" res); res
        
    /// Send a given reply over a AsyncReplyChannel, and also log the reply's contents
    let replyAndLog(rc:AsyncReplyChannel<'a>, (msg:'a)) =
        prStr "Replying" (sprintf "%A" msg)
        rc.Reply msg

    /// Updates the lastKnownCoord with a lock
    let updateLastKnownCoord k newV =
        hLock lastKnownCoord (fun _ ->
            lastKnownCoord.[k] <- newV
        )

    /// Enqueues all elements of a given sequence to the given queue
    let enqueueAll (q:Queue<'a>) seq =
        seq |> Seq.iter (fun e -> q.Enqueue(e))

    /// Determine if a given qc is already in the queuedClients queue
    let inQueuedClients qc =
     let s = Set.ofSeq (seq { for cid in queuedClients -> assert ((!queuedClientExps).[cid].IsSome)
                                                          let exp, ed, _ = (!queuedClientExps).[cid].Value
                                                          (cid, exp, ed) })
     let (cid, (exp, ed, rc)) = qc
     s.Contains (cid, exp, ed)

    /// Converts queued clients datastructure in a list of tuples
    let zipQueuedClients = fun() ->
        Seq.fold (fun lst cid ->
            assert (!queuedClientExps).[cid].IsSome
            (cid, (!queuedClientExps).[cid].Value) :: lst
        ) List.empty queuedClients

    /// Converts a list of tuples to the queued clients data structure
    let unzipQueuedClients zc =
        (!queuedClientExps) |> Array.iteri (fun i _ -> (!queuedClientExps).[i] <- None)
        queuedClients.Clear()
        zc |> List.rev |> Seq.iter (fun (c, exp) ->
            queuedClients.Enqueue(c)
            (!queuedClientExps).[c] <- Some(exp)
        )

    /// Queue client into the system
    let qcEnqueue cid edr =
        assert (not(queuedClients.Contains cid))
        queuedClients.Enqueue cid
        if (!queuedClientExps).[cid].IsSome then
            prStr2 "ENQUEUE" "WARNING: VALUE WAS NOT NONE"

        (!queuedClientExps).[cid] <- Some(edr)

    /// Dequeue client from system
    let qcDequeue = fun() ->
        let next = tryDequeue(queuedClients)
        if next.IsSome then
            let cid = next.Value
            let exp = (!queuedClientExps).[cid]
            assert exp.IsSome
            (!queuedClientExps).[cid] <- None
            Some(cid, exp.Value)
        else
            None

    /// Index of the lab currently owned by this class (or None)
    let labOwned = fun() -> Array.tryFindIndex (fun i -> i = clientID) lastKnownCoord

    /// Do we have a lab?
    let hasLab = fun() -> (labOwned()).IsSome

    /// Callback that is initiated when an OwnLab message gets a reply
    let aReplyOwnLab (inbox:MailboxProcessor<clientMsg>) lab v =
        prStr "GLOBAL async PostOwnLab callback" (sprintf "%A lab" v)

        hLock lastKnownCoord (fun _ ->
            let lo = labOwned()
            if lo.IsSome && lo.Value = lab && v <> clientID then
                failwith "Inconsistent lab information detected; will cause inconsistent state"
            else
                lastKnownCoord.[lab] <- v
        )

        let e = tryPeek(expsToRun)
        if e.IsSome && queuedClients.Count = 0 then
            let r = (!clients).[v].PostWantToDo e.Value clientID // possible bug?
            asyncStart r (fun w -> inbox.Post(ARplyWantDo(lab,v,w)))
        else
            prStr "GLOBAL" "Cancelled"

    /// Callback that is initiated when we get a reply regarding lab location
    let aReplyUpCoord lab v rc = 
        prStr "GLOBAL whoOwnsLab PostOwnLab callback" (sprintf "lab %A" v)

        hLock lastKnownCoord (fun _ ->
            let lo = labOwned()
            if lo.IsSome && lo.Value = lab && v <> clientID then
                failwith "Inconsistent lab information detected; will cause inconsistent state"
            else
                lastKnownCoord.[lab] <- v
        )

        replyAndLog(rc, v)

    /// Run when an experiment is complete
    let expComplete exp res =
        let expRes = tryDequeue(expsToRun)
        if expRes.IsSome then
            let doneExp = fst3 expRes.Value
            let doneRpy = thd3 expRes.Value

            if doneExp = exp then
                replyAndLog(doneRpy, res)
            else
                prStr "?" "We've recieved multiple ExpCompletes"

    /// Run when we're sent a WantToDo message
    let wantToDo edr cid rc =
        if not( inQueuedClients (cid, edr) ) then
            if queuedClients.Contains cid then
                prStr2 "wantToDo" "We already had an experiment for this client, replacing with this one"
                (!queuedClientExps).[cid] <- Some(edr)
            else
                qcEnqueue cid edr

            replyAndLog(rc, Queued)
        else
            replyAndLog(rc, AlreadyQueued)

    /// Function called to handle messages that have the same reply in every state
    let globalMessageHandling (inbox:MailboxProcessor<clientMsg>) msg =
      match msg with
      | ARplyWantDo(l, v, w) -> prStr "GLOBAL async PostWantToDo callback" (sprintf "%A wantDo" w)

                                if w = Queued || w = WillGift then
                                    queuedLabs.Add(l)
                                elif w = NoLab then
                                    prStr2 "!!!" (sprintf "Can't do %A in Lab %A" w l)
                                    queuedLabs.Remove(l) |> ignore
                                    asyncStart
                                        ((!clients).[v].PostOwnLab(l))
                                        (fun v -> aReplyOwnLab inbox l v)

      | ARplyExpDone(r, qc)  -> prStr "GLOBAL" (sprintf "res continuation callback; %A" r)

                                qc |> List.iter(fun (cid,(e,_,_)) ->
                                    prStr "GLOBAL" (sprintf "Telling %A who did %A" cid e)
                                    (!clients).[cid].PostExpComplete clientID r e
                                )

      | OwnLab(l, rc)        -> let o = lastKnownCoord.[l]

                                if o = clientID then
                                    replyAndLog(rc,o)
                                else
                                    asyncStart
                                        ((!clients).[o].PostOwnLab(l))
                                        (fun v -> aReplyUpCoord l v rc)

      | _                    -> failwith (sprintf "Unhandled message: %A not expected in this state" msg)

    /// Code to handle the mailbox messages
    let mailboxHandler (inbox:MailboxProcessor<clientMsg>) =
        let rec idle() = async { 
            let state = Idle
            prStr "IDLE" "Entered"

            if hasLab() then
                if queuedClients.Count > 0 then // We want to concede the lab
                    prStr "IDLE" "hasLab, queuedClients.Count > 0"
                    
                    let next = qcDequeue()
                    assert next.IsSome
                    let cid = fst next.Value
                    let exp = snd next.Value

                    if cid = clientID then
                        return! busy(Some(exp))
                    else
                        let lid = (labOwned()).Value

                        let r = (!clients).[cid].PostNowOwn lid (zipQueuedClients())

                        prStr2 "IDLE" (sprintf "Offering lab to next client %d" cid)
                        return! gifting (Some(r, cid, lid)) None 

                else
                    if expsToRun.Count > 0 then
                        prStr "IDLE" "hasLab, expsToRun.Count > 0"

                        let e = tryPeek(expsToRun)
                        assert e.IsSome

                        prStr "IDLE" (sprintf "%A" (e.Value))

                        return! busy(e)
                                                   

            prStr "IDLE" "Checking inbox..."                         
            let! msg = inbox.Receive()
            prStr "IDLE" (sprintf "Message: %A" msg)

            match msg with
            | WantToDo(edr, cid, rc) -> if hasLab() then
                                            prStr2 "IDLE" (sprintf "Offering lab to a message %d" cid)

                                            replyAndLog(rc, WillGift)

                                            let r = (!clients).[cid].PostNowOwn (labOwned()).Value (zipQueuedClients())
                                            return! gifting (Some(r, cid, (labOwned()).Value)) None

                                        else
                                            replyAndLog(rc, NoLab)

            | NewExp(e, d, rc)       -> expsToRun.Enqueue (e,d,rc)
                                        if hasLab() then
                                            prStr "IDLE" "Have lab"
                                            //Send "NowOwn" message when done
                                            let e = tryPeek(expsToRun)
                                            assert e.IsSome

                                            return! busy(e)
                                        else
                                            prStr "IDLE" "Don't have lab"
                                            return! waiting()


            | NowOwn(lid, cl, rc)    -> prStr "!!!IDLE" "NowOwn msg in idle state"
                                        replyAndLog(rc, DeclineOwnership)

            | ExpComplete(_,_,_)     -> prStr "IDLE" "Got ExpComplete, don't care"

            | Terminate              -> return! terminate()

            | _                      -> globalMessageHandling inbox msg

            return! idle() }



        /// The waiting state indicates the client has an experiment it wants to do and is waiting for a lab
        and waiting() = async { 
            let state = Waiting
            prStr "WAITING" "Entered"
                   
            if expsToRun.Count = 0 then
                failwith "We have entered the waiting state without experiments to run; will cause inconsistent state"               

            if queuedClients.Count = 0 then 
                prStr "WAITING" "We have experiments to run"

                hLock lastKnownCoord (fun _ ->
                    lastKnownCoord |> Seq.iteri (fun lab client ->
                        assert (lab < numLabs)
                        if not (queuedLabs.Contains lab) then
                            asyncStart
                                ((!clients).[client].PostOwnLab lab)
                                (fun v -> aReplyOwnLab inbox lab v)
                ))

            prStr "WAITING" "Checking inbox..."
            let! msg = inbox.Receive()
            prStr "WAITING" (sprintf "Message: %A" msg)

            match msg with
            | WantToDo(edr, cid, rc) -> printfn "VERY BAD: WantToDo in waiting state"
                                        replyAndLog(rc, NoLab)
                                        

            | NowOwn(lid, cl, rc)    -> if hasLab() then
                                            replyAndLog(rc, DeclineOwnership)

                                        else
                                            updateLastKnownCoord lid clientID
                                            replyAndLog(rc, AcceptOwnership)
                                                                        
                                            queuedLabs.Clear()

                                            assert (queuedClients.Count = 0)
                                            unzipQueuedClients cl

                                            let e = tryPeek(expsToRun)
                                            assert e.IsSome

                                            return! busy(e)

            | NewExp(e, d, rc)        -> expsToRun.Enqueue (e, d, rc)

            | ExpComplete(_,res,exp)  -> expComplete exp res
                                         return! idle()

            | Terminate               -> return! terminate()

            | _                       -> prStr2 "WAITING" (sprintf "%A" msg)
                                         globalMessageHandling inbox msg

            return! waiting() }



        /// The busy state indicates that the client is currently doing an experiment
        and busy(expIn) = async { 
            let state = Busy
            prStr "BUSY" "Entered"

            if not(hasLab()) then
                failwith "We have entered the busy state without a lab, or we have lost our lab due to inconsistent information"

            prStr "BUSY" (sprintf "labOwned: %A" (labOwned()))

            if expIn.IsSome then
                prStr "BUSY" (sprintf "expIn: %A" expIn.Value)

                let sufficient, doing =
                    bestExp
                        expIn.Value
                        (zipQueuedClients())
                        (labOwned()).Value
                        labs
                        clientID
                                            
                let inform = new List<queuedClient>(doing :: sufficient)

                // Add the current experiment to the list of informers if it isn't there already
                if not (List.ofSeq(inform) |> List.exists (fun (cl,_) -> cl = clientID)) then
                    inform.Add (clientID, expIn.Value)
          
                prStr "BUSY" (sprintf "Sufficient; %A" sufficient)

                let dExp, dDelay, _ = snd doing

                match labOwned() with
                | Some(lid:labID) -> prStr "BUSY" "Executing DoExp"

                                     (!labs).[lid].DoExp
                                        dDelay
                                        dExp
                                        clientID
                                        (fun res -> inbox.Post( ARplyExpDone(res, List.ofSeq inform) ))

                                     let oldQueuedClients = List.ofSeq queuedClients
                                     queuedClients.Clear()

                                     // Remove clients from the queue who the running experiment will suffice for
                                     // TODO: Should we be doing this here, or waiting until the experiment is complete?
                                     oldQueuedClients 
                                        |> Seq.filter (fun x -> 
                                            let exp = (!queuedClientExps).[x]
                                            if exp.IsSome then
                                                not (contains (x, exp.Value) sufficient)
                                            else
                                                false
                                           )
                                        |> Seq.iter (fun e -> queuedClients.Enqueue(e))

                                     prStr "BUSY" (sprintf "New clients; %A" (List.ofSeq queuedClients))                  
                                                                     
                | None            -> failwith "Tried to do exp without lab"

            prStr "BUSY" "Checking inbox..."
            let! msg = inbox.Receive()
            prStr "BUSY" (sprintf "Message: %A" msg)
                                          
            match msg with
            | WantToDo(edr, cid, rc) -> wantToDo edr cid rc                                                           

            | NowOwn(lid, cl, rc)    -> replyAndLog(rc, DeclineOwnership)

            | NewExp(e, d, rc)       -> expsToRun.Enqueue (e,d,rc)

            | ExpComplete(c, r, exp) -> if c = clientID then
                                            expComplete exp r
                                            return! idle()
                                        else
                                            prStr "BUSY" "Recieved ExpComplete not from us"
                                                                      
            | Terminate              -> return! terminate()

            | _                      -> globalMessageHandling inbox msg
                                                

            if not(hasLab()) then
                failwith "Inconsistent information has causes us to lose our lab; will cause inconsistent state"

            return! busy(None) }



        /// The gifting state indicates that the client is currently giving its lab to another client
        and gifting readyExp (queuedMessages:List<clientMsg> option) = async {
            let state = Gifting
            prStr "GIFTING" "Entered"

            if readyExp.IsSome then
                if (snd3 readyExp.Value) = clientID then
                    failwith "Attemping to gift self; will cause deadlock"

                let asy, cid, lid = readyExp.Value
                asyncStart asy (fun res -> inbox.Post( GiftComplete(lid, cid, res) ))

            // Create the queue if it doesn't already exist
            let queued = match queuedMessages.IsNone with
                         | true  -> new List<clientMsg>()
                         | false -> queuedMessages.Value


            if inbox.CurrentQueueLength = 0 && queued.Count > 0 then      
                prStr2 "GIFTING"  "Our queues are empty"
                                  
                queued |> Seq.iter (fun ms -> 
                    match ms with
                    | WantToDo(edr, cid, rc) -> wantToDo edr cid rc

                    | NowOwn(lid, cl, rc)    -> prStr2 "GIFTING" "NowOwn in GiftComplete"
                                                replyAndLog(rc, DeclineOwnership)

                    | _                      -> globalMessageHandling inbox ms
                 )

            prStr "GIFTING" "Checking inbox..."
            let! msg = inbox.Receive()
            prStr2 "GIFTING" (sprintf "Message: %A" msg)

            match msg with
            | NewExp(e, d, rc)      -> expsToRun.Enqueue(e, d, rc)
                           
            | ExpComplete(_, r, e)  -> expComplete e r

            | Terminate             -> return! terminate()

            | ARplyWantDo(_,_,_)
            | ARplyExpDone(_,_)     -> globalMessageHandling inbox msg

            | GiftComplete(l, c, r) -> if r = AcceptOwnership then
                                            prStr2 "GIFTING" "Lab transferred completed successfully"

                                            updateLastKnownCoord l c
                                            queuedClients.Clear()

                                            prStr2 "" (sprintf "%A" queuedClients)

                                            queued |> Seq.iter (fun msg -> 
                                                prStr2 "GIFTING"  "Responding to queued message"

                                                match msg with
                                                | WantToDo(edr, cid, rc) -> replyAndLog(rc, NoLab)

                                                | NowOwn(lid, cl, rc)    -> prStr2 "GIFTING" "ACCEPT - NowOwn"
                                                                            replyAndLog(rc, DeclineOwnership)   

                                                | _                      -> globalMessageHandling inbox msg
                                            )

                                            if expsToRun.Count > 0 then
                                                return! waiting()
                                            else
                                                return! idle()

                                        else if r = DeclineOwnership then
                                            prStr2 "GIFTING" "Lab transfer aborted" 

                                            queued |> Seq.iter (fun msg -> 
                                                prStr2 "GIFTING"  "Responding to queued message"

                                                match msg with
                                                | WantToDo(edr, cid, rc) -> wantToDo edr cid rc

                                                | NowOwn(lid, cl, rc)    -> prStr2 "GIFTING" "DECLINE - NowOwn"
                                                                            replyAndLog(rc, DeclineOwnership)

                                                | _                      -> globalMessageHandling inbox msg
                                            )

                                            return! idle()

            | _                     -> queued.Add(msg)
                                                                      
            return! gifting None (Some(queued)) }



        /// The termination state ceases all operation
        and terminate() = async { 
            let state = Termination
            Thread.Sleep(System.Threading.Timeout.Infinite) }
                
                              
        idle() // State we start in

    /// Asynchronous mailbox
    let mailbox = MailboxProcessor<clientMsg>.Start(mailboxHandler)
        
        
    member this.ClientID = clientID  // So other clients can find our ID easily
    member this.InitClients theClients theLabs = 
        clients:=theClients; labs:=theLabs
        queuedClientExps:=Array.init theClients.Length (fun _ -> None)

    member this.PostOwnLab (a:labID) = 
        assert (a < numLabs)
        mailbox.PostAndAsyncReply(fun x -> OwnLab(a,x))

    member this.PostWantToDo (edr:expDelayRes) (cid:clientID) =
        mailbox.PostAndAsyncReply(fun x -> WantToDo(edr,cid,x))

    member this.PostNowOwn (a:labID) (cl:queuedClient list) = 
        assert (a < numLabs)
        mailbox.PostAndAsyncReply(fun x -> NowOwn(a,cl,x))

    member this.PostExpComplete (cid:clientID) (r:expResult) (e:exp) =
        mailbox.Post(ExpComplete(cid,r,e))
    
    member this.DoExp busy exp =
        mailbox.PostAndReply(fun x -> NewExp(exp,busy,x))

    member this.Terminate() =
        mailbox.Post(Terminate)



//////////////////////////////////////////////////////////////// Top level testing code follows.      

// The following creates and initializes the instances of the lab and client classes
let mkClientsAndLabs numClients (labsRules: labRules list) = 
    let numLabs = labsRules.Length
    let clients = [| for i in 0..numClients-1 -> client (i, numLabs) |]
    let labs = [| for (i,rules) in List.zip [0..numLabs-1] labsRules -> lab (i,rules) |]
    Array.iter (fun (cl:client) -> cl.InitClients clients labs) clients
    (clients, labs)

let prClient cl pre str = prIndStr cl (sprintf "Host%d: %s" cl pre) str  // for client output



// Some simple testing code follows.  You almost certainly want to add your own tests to this.
// scheduledClient and randomTest are designed to make it easy to build other tests.

/// This function runs a test where the requests and times for each client are specified in a list (see below).
/// The list contains tuples (delayBeforeRequestTime, busyDoingExpTime, exp) in sequence.
let scheduledClient (clients:client[]) clID sched = mkThread ("Client"+string clID) <| fun () ->
    sched |> List.iteri (fun i (delay,busy,exp) ->
             sleep delay
             prClient clID "" (sprintf "requests %A with delay %d and busy %d" exp delay busy)
             prIndent clID (sprintf "Exp%d%c result:" clID (char (i+(int 'a')))) (clients.[clID].DoExp busy exp) |> ignore )
    
    prClient clID "COMPLETED EXPERIMENTS" ""
    
/// Run the threads for a test, and wait for them to finish.    
let doTest threads (clients:client[]) = startTime:=DateTime.Now
                                        prStamp -1 "Test started" ""
                                        List.iter (fun (th:Thread)-> th.Start()) threads
                                        List.iter (fun (th:Thread)-> th.Join()) threads
                                        //Seq.ofArray clients |> Seq.iter (fun c -> c.Terminate())
                                        prStamp -1 "" "ALL HOSTS COMPLETED"


// The following creates a random test via the scheduledTest class above.
let randBase() = match random 2 with 0->A | _->B

let rec randTerm () =     
    let rec intern maxDepth = match random 2, maxDepth with
                              | 1, _ -> randBase()
                              | _, 1 -> randBase()
                              | _ -> Mix (intern (maxDepth-1), intern (maxDepth-1))
    Mix (intern 2, intern 2)
 
/// Create a random test thread for a client-ID with the given average times and number of experiment requests.
let randomTestClient clients clID avgWait avgBusyTime numExp =
    scheduledClient clients clID 
       ( List.map (fun _ -> (random avgWait*2, random avgBusyTime*2, randTerm() )) [1..numExp] )

let randomTest avgWait avgBusyTime numExp numClients labsRules =
    let clients, _ = mkClientsAndLabs numClients labsRules 
    doTest [for i in 0..numClients-1 -> randomTestClient clients i avgWait avgBusyTime numExp  ] clients
  


/// Working test
do let clients, _ = mkClientsAndLabs 5 [rulesA; rulesB] 
   doTest [scheduledClient clients 0 [(0, 500, A)];     // Request a lab at the very start, use for "A" for 0.5 seconds
           scheduledClient clients 1 [(200, 300, Mix (Mix (A,Mix (A,A)),B))] ;   // Request after 0.2s, release 0.3s later.
           
           scheduledClient clients 2 [(100, 200, Mix (A,Mix (A,A)))];   // These three will all be waiting for a lab.
           scheduledClient clients 3 [(400, 200, Mix (A,A))];           // Client 2 should include the others as guests.
           scheduledClient clients 4 [(400, 200, A)]
          ] clients


//randomTest 10 50 4 8 [rulesB; rulesB] |> ignore            // A smaller random test.
//randomTest 5 20 5 20 [rulesA; rulesB; rulesC] |> ignore    // A larger random test.
