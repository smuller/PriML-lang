structure Thread :> THREAD =
struct

structure T = MLton.Thread
structure P = Priority
structure Bag = ListBag

exception Thread
exception IncompatiblePriorities

datatype 'a result =
         Waiting
         | Finished of 'a * int (* result, depth *)
         | Raised of exn * int

fun writeResult fr f =
    let val r = f ()
        val d = getDepth (processorNumber ())
    in
        fr := Finished (r, d)
    end
    handle e => fr := Raised (e, getDepth (processorNumber ()))

type 'a t =
     {
       result : 'a result ref,
       prio   : P.t,
       bag    : (P.t * Task.t) Bag.t,
       hand   : Q.hand option,
       cancel : Cancellable.t,
       thunk  : unit -> 'a
     }

fun run (fr, bag) f (r, hand) =
    ( writeResult fr f;
      (case Bag.dump bag of
           NONE => raise Thread
         | SOME l => List.app (ignore o push) l);
      (* if tryRemove (r, hand) then
          (* parent hasn't been stolen; switch to it *)
          switchTo hand
      else *)
          returnToSched ()
    )

fun spawn f r' =
    let val fr = ref Waiting
        val bag = Bag.new ()
        val c = Cancellable.new ()
        val _ = pushCC  (r', c, run (fr, bag) f)
    in
        { result = fr, prio = r', bag = bag, hand = NONE, cancel = c,
          thunk = f}
    end
        (*
    let
        val p = processorNumber ()
        val r = curPrio p
        val fr = ref Waiting
        val bag = Bag.new ()
        val task = newTask (Task.Thunk (run (fr, bag) f))
        val hand = (if P.pe (r, r') then push else insert) (r', task)
        val c = Task.cancellable task
    in
        {result = fr, prio = r', bag = bag, hand = hand, cancel = c, thunk = f}
    end
*)

fun poll ({result, bag, ...} : 'a t) =
    if not (Bag.isDumped bag) then NONE
    else case !result of
             Finished (x, _) => SOME x
           | Raised (e, _) => raise e
           | Waiting => raise Thread

fun sync {result, prio, bag, hand, cancel, thunk} =
    let val c = if Cancellable.isCancelled cancel then
                    raise Thread
                else
                    ()
        val p = processorNumber ()
        val r = curPrio p
        val _ = if P.ple (r, prio) then ()
                else
                    raise IncompatiblePriorities
        fun f rt =
            if Bag.insert (bag, rt) then
                (* Successfully waiting on the thread *)
                ()
            else
        (* Bag was just dumped, so we can directly add the task *)
                ignore (push rt)
        val d = getDepth p
        val _ = case !result of
                    Waiting => suspend f
                  | _ => ()
    in
        case !result of
            Finished (x, d') => (setDepth (p, Int.max (d, d') + 1); x)
          | Raised (e, d') => (setDepth (p, Int.max (d, d') + 1); raise e)
          | Waiting => raise Thread
    end

fun fork (f, g) = raise Thread (*
    let val r = curPrio (processorNumber ())
        val (gt as {hand, ...}) = spawn g r
        val fr = f ()
        val gr = if tryRemove (r, hand) then
                     g ()
                 else
                     sync gt
    in
        (fr, gr)
    end *)

fun cancel ({cancel, ...} : 'a t) =
    Cancellable.cancel cancel
end

structure Priority = Priority
structure IO = IO

structure Basic =
struct
val init = init
val finalizePriorities = finalizePriorities
fun currentPrio () = curPrio (processorNumber ())
val numberOfProcessors = numberOfProcessors
val processorNumber = processorNumber
val suspend = suspend
val suspendIO = suspendIO
end
