-------------------- MODULE WriteThrough --------------------
EXTENDS Integers, TLC, FiniteSets, Sequences

CONSTANTS Key, Value, Oid, None

VARIABLES db

VARIABLES cache

\* operations
VARIABLES ops

\* lps: linearizable points, used to verify the linearizability
VARIABLES lps

-------------------------------------------------------------
InitValue ≜ CHOOSE v ∈ Value: TRUE

OpStatus ≜
    { "Pending"  \* New request
    , "Reading"  \* Reading from DB
    , "Writing"  \* Writing to DB
    , "Updating" \* Updating cache
    , "Done"     \* Finished
    , "Failed"   \* Unfinished
    }

OpType ≜ { "Read", "Write" }

NewOp(t, k, v) ≜
    [ status ↦ "Pending"
    , type ↦ t
    , key ↦ k
    , value ↦ None
    ]

UpdateStatus(op, status) ≜ [ op EXCEPT !.status = status ]

\* Read value from cache, and return the finished operation
ReadFromCache(oid) ≜
    LET op ≜ ops[oid]
        value ≜ cache[op.key]
    IN [ op EXCEPT !.status = "Done", !.value = value ]

IssueNewRequest(oid) ≜
    ∧ oid ∉ DOMAIN ops
    ∧ ∃key ∈ Key, type ∈ OpType:
        IF type = "Read"
        THEN ops' = oid :> NewOp(type, key, None) @@ ops
        ELSE ∃value ∈ Value:
                ops' = oid :> NewOp(type, key, value) @@ ops
    ∧ UNCHANGED ⟨db, cache, lps⟩

NoRunningOps ≜
    ¬ ∃oid ∈ DOMAIN ops:
        ops[oid].status ∈ { "Reading", "Writing", "Updating" }

HandleReadRequest(oid) ≜
    ∧ oid ∈ DOMAIN ops
    ∧ ops[oid].status = "Pending"
    ∧ ops[oid].type = "Read"
    ∧ IF ops[oid].key ∈ DOMAIN cache
      \* key in cache, return immediately
      THEN LET fop ≜ ReadFromCache(oid)
           IN ∧ ops' = [ ops EXCEPT ![oid] = fop ]
              ∧ lps' = Append(lps, fop)
      \* key not in cache, try to read from db
      \*    if there are not other running operations.
      ELSE ∧ NoRunningOps
           ∧ ops' = [ ops EXCEPT ![oid].status = "Reading" ]
           ∧ UNCHANGED ⟨lps⟩
    ∧ UNCHANGED ⟨db, cache⟩

ReadDB(oid) ≜
    ∧ oid ∈ DOMAIN ops
    ∧ ops[oid].status = "Reading"
    ∧ ops' = [ ops EXCEPT ![oid].status = "Updating",
                          ![oid].value = db[ops[oid].key] ]
    ∧ UNCHANGED ⟨db, cache, lps⟩

HandleWriteRequest(oid) ≜
    ∧ oid ∈ DOMAIN ops
    ∧ ops[oid].status = "Pending"
    ∧ ops[oid].type = "Write"
    ∧ NoRunningOps
    ∧ ops' = [ ops EXCEPT ![oid].status = "Writing" ]
    ∧ UNCHANGED ⟨db, cache, lps⟩

WriteDB(oid) ≜
    ∧ oid ∈ DOMAIN ops
    ∧ ops[oid].status = "Writing"
    ∧ ops' = [ ops EXCEPT ![oid].status = "Updating" ]
    ∧ db' = [ db EXCEPT ![ops[oid].key] = ops[oid].value ]
    ∧ UNCHANGED ⟨cache, lps⟩

UpdateCache(oid) ≜
    ∧ oid ∈ DOMAIN ops
    ∧ ops[oid].status = "Updating"
    ∧ cache' = ops[oid].key :> ops[oid].value @@ cache
    ∧ ops' = [ ops EXCEPT ![oid].status = "Done" ]
    ∧ lps' = Append(lps, ops[oid])
    ∧ UNCHANGED ⟨db⟩

DeleteCache ≜ ∃key ∈ Key:
    ∧ key ∈ DOMAIN cache
    ∧ cache' = [ k ∈ DOMAIN cache \ { key } ↦ cache[k] ]
    ∧ UNCHANGED ⟨db, ops, lps⟩

ShouldBeDone(op) ≜ op.type = "Write" ∧ op.status = "Updating"

MapCrashedOp(op) ≜
    CASE op.type = "Read" ∧ op.status ∈ {"Reading", "Updating"}
                → UpdateStatus(op, "Unfinished")
       □ op.type = "Write" ∧ op.status = "Writing"
                → UpdateStatus(op, "Unfinished")
       □ ShouldBeDone(op)
                → UpdateStatus(op, "Done")
       □ OTHER → op

Done ≜ ∀oid ∈ DOMAIN ops: ops[oid].status ∈ { "Done", "Unfinished" }

RestartCache ≜
    ∧ ¬ Done
    ∧ cache' = ⟨⟩
    ∧ ops' = [ oid ∈ DOMAIN ops ↦ MapCrashedOp(ops[oid]) ]
    ∧ LET opp ≜ { oid ∈ DOMAIN ops: ShouldBeDone(ops[oid]) }
      IN IF opp = {}
         THEN UNCHANGED ⟨lps⟩
         ELSE lps' = Append(lps, ops[CHOOSE oid ∈ opp: TRUE])
    ∧ UNCHANGED ⟨db⟩

AvoidDeadlock ≜
    ∧ Done
    ∧ UNCHANGED ⟨db, cache, ops, lps⟩

Init ≜
    ∧ db = [ k ∈ Key ↦ InitValue ]
    ∧ cache = ⟨⟩
    ∧ ops = ⟨⟩
    ∧ lps = ⟨⟩

Next ≜
    ∨ ∃oid ∈ Oid:
        ∨ HandleReadRequest(oid)
        ∨ HandleWriteRequest(oid)
        ∨ ReadDB(oid)
        ∨ WriteDB(oid)
        ∨ UpdateCache(oid)
        ∨ IssueNewRequest(oid)
    ∨ RestartCache
    ∨ DeleteCache
    ∨ AvoidDeadlock

Spec ≜ Init ∧ □[Next]_⟨db, cache, ops, lps⟩ ∧ WF_⟨db, cache, ops, lps⟩(Next)

-------------------------------------------------------------

RECURSIVE CheckLps(_, _, _)
CheckLps(l, pos, env) ≜
    CASE pos > Len(l) → TRUE
       □ l[pos].status = "Unfinished" → CheckLps(l, pos+1, env)
       □ l[pos].type = "Read" → ∧ l[pos].value = env[l[pos].key]
                                ∧ CheckLps(l, pos+1, env)
       □ OTHER → CheckLps(l, pos+1, l[pos].key :> l[pos].value @@ env)

Liveness ≜ ◇(Done)
Safety ≜ Done ⇒ CheckLps(lps, 1, [ k ∈ Key ↦ InitValue ])

=============================================================
