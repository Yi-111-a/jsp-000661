# Harness log

- date: 2026-09-18T19:37:43Z
- sha: 37fafb7f2e925db577551515140f74bacc4a469c
- toolchain: leanprover/lean4:v4.34.0

## lake build
```
⚠ [1080/1115] Replayed Jsp000661.Defs
warning: Jsp000661/Defs.lean:28:0: automatically included section variable(s) unused in theorem `SimpleGraph.LocallyLargeIndep.on`:
  [DecidableEq V]
  [DecidableRel G.Adj]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq V] [DecidableRel G.Adj] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: Jsp000661/Defs.lean:31:0: automatically included section variable(s) unused in theorem `SimpleGraph.IsIndepSet.subset'`:
  [DecidableEq V]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq V] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [3113/3116] Replayed Jsp000661.Counting
warning: Jsp000661/Counting.lean:40:0: automatically included section variable(s) unused in theorem `SimpleGraph.indepSets_card_lower`:
  [DecidableRel G.Adj]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableRel G.Adj] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (3116 jobs).
exit=0
```

## sorry/admit count
sorry_or_admit=0

## #print axioms
```
'SimpleGraph.indepNumber_of_locally_large' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**RESULT: GREEN**
