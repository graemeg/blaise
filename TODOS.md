# TODOS

Deferred work captured during reviews. Each item states what, why, and where to start.

## Lazy enumerable pipelines (functional collections)

- **What:** Deferred `Map`/`Where`/`Take`/`Skip` pipelines over `Generics.Collections`
  that do not allocate intermediate lists — an iterator/enumerator protocol that
  composes with `for..in` (e.g. `People.Where(IsAdult).Map(NameOf)` evaluates lazily,
  one element at a time, with no temporary `TList<T>` per stage).
- **Why:** Eager LINQ-lite (E2, accepted into `docs/anonymous-methods-design.adoc`)
  allocates a new collection per stage. For large collections or long chains that is
  wasteful; lazy pipelines make chained transforms cheap and is the "ideal" form of
  the functional layer.
- **Pros:** Allocation-free chains; composes naturally with `for..in`; the expected
  shape for anyone coming from LINQ / Kotlin sequences / Java streams.
- **Cons:** Needs an iterator/enumerator protocol that does not exist yet — a
  meaningfully bigger lift than eager ops. Lazy evaluation also has sharper edges
  (deferred exceptions, single-enumeration gotchas).
- **Context:** Surfaced in the 2026-06-30 `/plan-ceo-review` of
  `docs/anonymous-methods-design.adoc` as expansion item **E4**, deferred while E1
  (type vocabulary), E2 (eager ops), E3 (lambda Sort), and E5 (`->` syntax) were
  accepted. Start once the closure primitive (Phases 0-7) and the eager functional
  layer (Phases 8-10) land — lazy pipelines are their natural successor.
- **Depends on:** anonymous-methods primitive (closures) + E1 type vocabulary; an
  iterator/enumerator protocol (`for..in` over a user enumerator) which may itself
  need a small language/RTL design of its own.
