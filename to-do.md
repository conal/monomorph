
*   Keep noodling over simple & robust `standardizeCon`.*   Connect with rest of compiler.
*   Generate circuits again, but *much* larger this time.
*   Experiment with annotations, per-module and/or per-definition.
*   Look again at simplifying the `Rep`-related signatures.
    Maybe the casts could be shifted a crossed let boundaries and lambdas and still cancel out.
    I was reluctant to replicate casts, because I worried about exponentially many copies.
    Now I am doubtful that they would float more than one level and hopeful that they would meet their opposites and cancel out.

*   Blog.


*   Look for faster implementation of `simplifyWithLetFloatingR`.
*   Figure out how `unfoldPoly` sometimes captures value arguments, and fix it.
*   Detect external polymorphism and fail with a message.


Done:

*   Try simplifying the signatures of `abst'` and `repr'` (and maybe `abst`and `repr`) to hide the `Eq#`.
    I re-disovered that this simpler type leads to more casts remaining in programs.
    I abandoned the changed `Circat.Rep` in a new circat branch called "simpler-method-signatures".
*   Rework the plugin for use directly by GHC, without the hermit REPL.

